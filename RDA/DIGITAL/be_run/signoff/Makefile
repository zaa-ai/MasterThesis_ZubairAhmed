FLOW_CHECK  = "$(PROJECT_HOME)/scripts/misc/sh/flow_check.sh"
SCRIPTS_DIR = "$(PROJECT_HOME)/scripts/signoff"
TOP_MODULE  = "digtop"

LOGS_DIR = logs
RESULTS_DIR = results
#StarRC setup
STARRC_EXEC   = StarXtract
TOP_DESIGN = digtop
TECH_LIB_PATH = $(shell getPrjCfg.rb -p config/tech)

#getting Library related variables from tech_config.xml
TECH_MAP_FILE = $(shell getPrjCfg.rb -r $(TECH_LIB_PATH) -p tech/phys/mapfile)
# Additional setup for StarRC Simultaneous Multicorner Extraction flow (SMC)
# Corner Names
#CORNER_NAME_MAX = $(shell getPrjCfg.rb -r $(TECH_LIB_PATH) tech/lib/max/oc)
#CORNER_NAME_MIN = $(shell getPrjCfg.rb -r $(TECH_LIB_PATH) tech/lib/min/oc)
CORNER_NAME_MAX = WCCOM
CORNER_NAME_MIN = LTCOM
# NXTGRD_FILES
TCAD_GRD_FILE_MAX = $(shell getPrjCfg.rb -r $(TECH_LIB_PATH) -p tech/phys/extract)
TCAD_GRD_FILE_MIN = $(shell getPrjCfg.rb -r $(TECH_LIB_PATH) -p tech/phys/extract)
# Corner Temperatures
TEMP_MAX = 150
TEMP_MIN = -40

# To $CORNER_NAM_... corresponding library names (needed for set_operating_condition in pt_operating_condition)
LIBRARY_NAME_MAX = $(shell getPrjCfg.rb -r $(TECH_LIB_PATH) tech/lib/max/name)
LIBRARY_NAME_MIN = $(shell getPrjCfg.rb -r $(TECH_LIB_PATH) tech/lib/min/name)

MAX_SPEF_FILE = ./results/digtop.starrc.spef.WCCOM.gz
MIN_SPEF_FILE = ./results/digtop.starrc.spef.LTCOM.gz

SCENARIOS = func_min func_max scan_min scan_max
SCENARIOS_BRIDGE = bridge_scan_min bridge_scan_max

ifndef DEBUG
 DEBUG=0
endif
ifndef QUIT
 export QUIT=1
endif

THIS_TARGET=$@

FOLDERS = logs results reports

help:
	@echo " "
	@echo " Makefile help"
	@echo " ============="
	@echo " "
	@echo " usage: make TARGET "
	@echo " "
	@echo " *** TARGET:"
	@echo " clean			remove all "
	@echo " clean_all		remove all "
	@echo " -----------------------------------------------"
	@echo " pt			Run Primetime Flow"
	@echo " -----------------------------------------------"
	@echo " dmsa		Run Primetime Flow with dmsa"
	@echo " -----------------------------------------------"
	@echo " extract		Run StarRC Extraction"
	@echo " -----------------------------------------------"
	@echo " bridge		Run StarRC Extraction for bridge file generation"
	@echo " -----------------------------------------------"
	@echo " lic			check for availability of licenses"
	@echo " -----------------------------------------------"
	@echo " "

##Clean
clean_all: clean
	rm  -f pt extract *.log extract bridge
	rm -rf logs results reports 

clean: 
	rm -rf .nodeIdDynamicRanges .tech_file.asc.lck .tech_file.lock
	rm -rf chip_finish_icc.* outputs_icc.*
	rm -rf star*
	rm -rf work*

pt: $(FOLDERS)
	export SCENARIO=func_min; pt_shell -f user_tcl/sta.tcl | tee -i logs/func_min.log; mv parasitics_command.log logs/parasitics_command_func_min.log
	export SCENARIO=func_max; pt_shell -f user_tcl/sta.tcl | tee -i logs/func_max.log; mv parasitics_command.log logs/parasitics_command_func_max.log
	export SCENARIO=scan_min; pt_shell -f user_tcl/sta.tcl | tee -i logs/scan_min.log; mv parasitics_command.log logs/parasitics_command_scan_min.log
	export SCENARIO=scan_max; pt_shell -f user_tcl/sta.tcl | tee -i logs/scan_max.log; mv parasitics_command.log logs/parasitics_command_scan_max.log
	#gunzip results/*.func_*.sdf.gz
	#$(PROJECT_HOME)/scripts/misc/rb/patch_sdf_sync_ffs.rb -o -t -f results/*.func_*.sdf -s i_utils_sync_ff_re -s i_utils_sync_ff_fe
	#gzip results/*.func_*.sdf
	#@$(FLOW_CHECK) logs/*.log $@

dmsa: $(FOLDERS)
	pt_shell -multi_scenario -f user_tcl/dmsa.tcl | tee -i logs/dmsa.log
	$(foreach scen,$(SCENARIOS),mv work/$(scen)/out.log logs/$(scen).log;)
	$(foreach scen,$(SCENARIOS),mv work/$(scen)/parasitics_command.log logs/parasitics_command_$(scen).log;)
	$(foreach scen,$(SCENARIOS),mv work/$(scen)/results/$(TOP_DESIGN).signoff.sdf.gz results/$(TOP_DESIGN).$(scen).signoff.sdf.gz;)
	$(foreach scen,$(SCENARIOS),mv work/$(scen)/reports/$(TOP_DESIGN)_report_global_slack.report reports/$(TOP_DESIGN)_$(scen)_report_global_slack.report;)
	tar cjf reports/signoff.tar.bz2 work
	#gunzip results/*.func_*.sdf.gz
	#$(PROJECT_HOME)/scripts/misc/rb/patch_sdf_sync_ffs.rb -o -t -f results/*.func_*.sdf -s i_utils_sync_ff_re -s i_utils_sync_ff_fe
	#gzip results/*.func_*.sdf
	@$(FLOW_CHECK) logs/*.log $@

dmsa_bridge: $(FOLDERS)
	pt_shell -multi_scenario -f user_tcl/dmsa_bridge.tcl | tee -i logs/dmsa_bridge.log
	$(foreach scen,$(SCENARIOS_BRIDGE),mv work_bridge/$(scen)/out.log logs/$(scen).log;)
	$(foreach scen,$(SCENARIOS_BRIDGE),mv work_bridge/$(scen)/parasitics_command.log logs/parasitics_command_$(scen).log;)
	$(foreach scen,$(SCENARIOS_BRIDGE),mv work_bridge/$(scen)/results/$(TOP_DESIGN).signoff.sdf.gz results/$(TOP_DESIGN).$(scen).signoff.sdf.gz;)

extract: $(FOLDERS)
	m4 -DTCAD=$(TCAD_GRD_FILE_MIN) \
       -DMAP=$(TECH_MAP_FILE) \
       -DTOPLEVEL=$(TOP_MODULE) \
       -DCORNER=$(CORNER_NAME_MIN) -DTEMP=$(TEMP_MIN) \
       $(SCRIPTS_DIR)/template/starrc/star_cmd_gate.tpl > ./results/star_cmd_gate_min.cmd
	m4 -DTCAD=$(TCAD_GRD_FILE_MAX) \
       -DMAP=$(TECH_MAP_FILE) \
       -DTOPLEVEL=$(TOP_MODULE) \
       -DCORNER=$(CORNER_NAME_MAX) -DTEMP=$(TEMP_MAX) \
       $(SCRIPTS_DIR)/template/starrc/star_cmd_gate.tpl > ./results/star_cmd_gate_max.cmd
	@echo "--> Run MIN Reference Extraction"
	$(STARRC_EXEC) ./$(RESULTS_DIR)/star_cmd_gate_min.cmd
	@echo "--> Run MAX Reference Extraction"
	$(STARRC_EXEC) ./$(RESULTS_DIR)/star_cmd_gate_max.cmd
	date > extract

bridge: #outputs_icc
	m4 -DTCAD=$(TCAD_GRD_FILE_MIN) \
       -DMAP=$(TECH_MAP_FILE) \
       -DTOPLEVEL=${TOP_MODULE} \
	$(SCRIPTS_DIR)/template/starrc/bridge.tpl  > ./results/bridge.cmd
	$(STARRC_EXEC) -clean 	 ./results/bridge.cmd | tee $(LOGS_DIR)/star_bridge.log
	date > bridge

lic:
	lmstat -f PrimeTime
	lmstat -f PrimeTime-SI
	lmstat -f PrimePower

all:
	@make extract
	@make bridge
	@make dmsa

################################################################################################################
# Init folders
################################################################################################################
$(FOLDERS):
	@echo "Creating Folder \"$@\""
	@mkdir -p $@

################################################################################################################
# export all variables to sub processes
################################################################################################################
.EXPORT_ALL_VARIABLES:
		   
