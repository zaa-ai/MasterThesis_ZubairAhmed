FLOW_CHECK="$(PROJECT_HOME)/scripts/misc/sh/flow_check.sh"
TMAX_ROOT=$(shell which tmax)/../..
TMAX=tmax2

WGL_GZIP = "$(shell find ./results/ -name '*.wgl' | xargs gzip)"
GEN_COV  = "$(PROJECT_HOME)/scripts/misc/perl/gen_atpg_cov_rpt.pl"

SYN_RESULTS_DIR       = $(PROJECT_HOME)/be_run/syn/results
NONDFT_SIGNAL_FILES   = $(SYN_RESULTS_DIR)/$(wildcard nonDFT*)
SCAN_PROTOCOL_FILES   = $(SYN_RESULTS_DIR)/digtop.mapped.scancompress.spf
SCAN_PROTOCOL_FILES  += $(SYN_RESULTS_DIR)/digtop.mapped.scan.spf
SCAN_PROTOCOL_FILES  += $(SYN_RESULTS_DIR)/digtop.mapped.iddq.spf
BRIDGE_FILE_RM_OUTPUT = $(PROJECT_HOME)/be_run/signoff/results/bridge.file
SLACK_FILE_RM_OUTPUT  = $(PROJECT_HOME)/be_run/signoff/reports/digtop_scan_max_report_global_slack.report

###########################################
# Simulation Setup for Pattern Simulations
###########################################

LOGS_DIR            = "$(PROJECT_HOME)/be_run/test/logs"
LAYOUT_RESULTS_DIR  = "$(PROJECT_HOME)/be_run/layout/results"
SIGNOFF_RESULTS_DIR = "$(PROJECT_HOME)/be_run/signoff/results"
PATTERN_RESULTS_DIR = "$(PROJECT_HOME)/be_run/test/results"


TECH_LIB_PATH       = $(shell getPrjCfg.rb -p config/tech)
LIB_FILES           = $(shell getPrjCfg.rb -r $(TECH_LIB_PATH) -p tech/sim_hdl/none)
SIMOPTIONS          = -q -sverilog +neg_tchk -negdelay +sdfverbose +define+SCAN+RECREM+NTC +lint=TFIPC-L
#SIMOPTIONS        =-q -sverilog +neg_tchk +sdfverbose +define+SCAN +lint=TFIPC-L +define+tmax_diag=2
ifeq (1, $(GUI))
SIMOPTIONS         += -kdb -debug -gui
endif
#SIMOPTIONS         += +define+tmax_diag=2

ifndef WRAPPER
  WRAPPER=
  DESIGN_NAME = "digtop"
  TOP_MODULE  = "digtop_tb/dut"
  ADDITIONAL_LIB_FILES=
else
  WRAPPER = "TRUE"
  DESIGN_NAME = "asic_shell"
  # Path do design in the TBENCH_* files, used for sdf-Annotation in VSC pattern simulation
  TOP_MODULE  = "digtop_tb/dut/asic_inst/xdigtop"
  ADDITIONAL_LIB_FILES=-f ../hdl/files.f
endif
ifndef DIFF
  DIFF=0
endif

NETLIST_FILES="$(LAYOUT_RESULTS_DIR)/digtop.output.v" 
NETLIST_FILES_SYN="$(LAYOUT_RESULTS_DIR)/digtop.mapped.v"


TBENCH_FILE_CELL_STUCK = "$(PATTERN_RESULTS_DIR)/$(DESIGN_NAME)_cell_stuck.comp.maxtb.v"
TBENCH_FILE_CELL_TRANS = "$(PATTERN_RESULTS_DIR)/$(DESIGN_NAME)_cell_trans.comp.maxtb.v"
TBENCH_FILE_DYNBR      = "$(PATTERN_RESULTS_DIR)/$(DESIGN_NAME)_dynbr.comp.maxtb.v"
TBENCH_FILE_DYN        = "$(PATTERN_RESULTS_DIR)/$(DESIGN_NAME)_dyn.comp.maxtb.v"
TBENCH_FILE_STABR      = "$(PATTERN_RESULTS_DIR)/$(DESIGN_NAME)_stabr.comp.maxtb.v"
TBENCH_FILE_STAT       = "$(PATTERN_RESULTS_DIR)/$(DESIGN_NAME)_stat.comp.maxtb.v"
TBENCH_FILE_STUCK      = "$(PATTERN_RESULTS_DIR)/$(DESIGN_NAME)_stuck.comp.maxtb.v"
TBENCH_FILE_TRANS      = "$(PATTERN_RESULTS_DIR)/$(DESIGN_NAME)_trans.comp.maxtb.v"
TBENCH_FILE_IDDQ       = "$(PATTERN_RESULTS_DIR)/$(DESIGN_NAME)_iddq.scan.maxtb.v"


SDFMAX=$$(ls $(SIGNOFF_RESULTS_DIR)/digtop.scan_max.signoff.sdf.gz)
SDFMIN=$$(ls $(SIGNOFF_RESULTS_DIR)/digtop.scan_min.signoff.sdf.gz)

ifndef DEBUG
 DEBUG=0
endif
ifndef QUIT
 export QUIT=1
endif

FOLDERS = logs logs/tmax results reports stil

help:
	@echo " "
	@echo " Makefile help"
	@echo " ============="
	@echo " "
	@echo " usage: make TARGET "
	@echo " "
	@echo " *** TARGET:"
	@echo " pattern              generate pattern"
	@echo " pattern_syn          generate pattern of synthesis netlist"
	@echo " simmax               simulate all pattern with sdf annotaded in max corner, add GUI=1 to run with gui"
	@echo " simmin               simulate all pattern with sdf annotaded in min corner, add GUI=1 to run with gui"
	@echo " clean                remove all "
	@echo " clean_all            remove all "


pattern: patch_spf
	@make -s $(FOLDERS)
	$(TMAX) -shell -tcl user_tcl/test.tcl | tee -i logs/$@.log
	@$(FLOW_CHECK) logs/$@.log $@
	@$(GEN_COV) -l logs/pattern.log	

# Run on synthesis netlist for fault coverage improvement...
pattern_syn:
	@make -s $(FOLDERS)
	$(TMAX) -shell -tcl user_tcl/test_syn.tcl | tee -i logs/$@.log
	@$(FLOW_CHECK) logs/$@.log $@

simmax:
	mkdir -p logs/vcs
	mkdir -p ./maxrun
	cd maxrun; vcs -R $(SIMOPTIONS) -sdf max:$(TOP_MODULE):$(SDFMAX) -l $(LOGS_DIR)/vcs/vcs_dyn_max.log        ${TBENCH_FILE_DYN}  ${ADDITIONAL_LIB_FILES} ${LIB_FILES} ${NETLIST_FILES}
	cd maxrun; vcs -R $(SIMOPTIONS) -sdf max:$(TOP_MODULE):$(SDFMAX) -l $(LOGS_DIR)/vcs/vcs_stat_max.log       ${TBENCH_FILE_STAT} ${ADDITIONAL_LIB_FILES} ${LIB_FILES} ${NETLIST_FILES}
	cd maxrun; vcs -R $(SIMOPTIONS) -sdf max:$(TOP_MODULE):$(SDFMAX) -l $(LOGS_DIR)/vcs/vcs_iddq_max.log       ${TBENCH_FILE_IDDQ} ${ADDITIONAL_LIB_FILES} ${LIB_FILES} ${NETLIST_FILES}
#	cd maxrun; vcs -R $(SIMOPTIONS) -sdf max:$(TOP_MODULE):$(SDFMAX) -l $(LOGS_DIR)/vcs/vcs_cell_stuck_max.log ${TBENCH_FILE_CELL_STUCK} ${ADDITIONAL_LIB_FILES} ${LIB_FILES} ${NETLIST_FILES}
#	cd maxrun; vcs -R $(SIMOPTIONS) -sdf max:$(TOP_MODULE):$(SDFMAX) -l $(LOGS_DIR)/vcs/vcs_cell_trans_max.log ${TBENCH_FILE_CELL_TRANS} ${ADDITIONAL_LIB_FILES} ${LIB_FILES} ${NETLIST_FILES}
#	cd maxrun; vcs -R $(SIMOPTIONS) -sdf max:$(TOP_MODULE):$(SDFMAX) -l $(LOGS_DIR)/vcs/vcs_dynbr_max.log      ${TBENCH_FILE_DYNBR}      ${ADDITIONAL_LIB_FILES} ${LIB_FILES} ${NETLIST_FILES}
#	cd maxrun; vcs -R $(SIMOPTIONS) -sdf max:$(TOP_MODULE):$(SDFMAX) -l $(LOGS_DIR)/vcs/vcs_stabr_max.log      ${TBENCH_FILE_STABR}      ${ADDITIONAL_LIB_FILES} ${LIB_FILES} ${NETLIST_FILES}
#	cd maxrun; vcs -R $(SIMOPTIONS) -sdf max:$(TOP_MODULE):$(SDFMAX) -l $(LOGS_DIR)/vcs/vcs_stuck_max.log      ${TBENCH_FILE_STUCK}      ${ADDITIONAL_LIB_FILES} ${LIB_FILES} ${NETLIST_FILES}
#	cd maxrun; vcs -R $(SIMOPTIONS) -sdf max:$(TOP_MODULE):$(SDFMAX) -l $(LOGS_DIR)/vcs/vcs_trans_max.log      ${TBENCH_FILE_TRANS}      ${ADDITIONAL_LIB_FILES} ${LIB_FILES} ${NETLIST_FILES}
	date > simmax

simmin:
	mkdir  -p $(LOGS_DIR)/vcs
	mkdir -p ./minrun
	cd ./minrun
	cd minrun; vcs -R $(SIMOPTIONS) -sdf min:$(TOP_MODULE):$(SDFMIN) -l $(LOGS_DIR)/vcs/vcs_stat_min.log       ${TBENCH_FILE_STAT} ${ADDITIONAL_LIB_FILES}      ${LIB_FILES} ${NETLIST_FILES}
	cd minrun; vcs -R $(SIMOPTIONS) -sdf min:$(TOP_MODULE):$(SDFMIN) -l $(LOGS_DIR)/vcs/vcs_dyn_min.log        ${TBENCH_FILE_DYN}  ${ADDITIONAL_LIB_FILES}      ${LIB_FILES} ${NETLIST_FILES}
	cd minrun; vcs -R $(SIMOPTIONS) -sdf min:$(TOP_MODULE):$(SDFMIN) -l $(LOGS_DIR)/vcs/vcs_iddq_min.log       ${TBENCH_FILE_IDDQ} ${ADDITIONAL_LIB_FILES}      ${LIB_FILES} ${NETLIST_FILES}
#	cd minrun; vcs -R $(SIMOPTIONS) -sdf min:$(TOP_MODULE):$(SDFMIN) -l $(LOGS_DIR)/vcs/vcs_cell_stuck_min.log ${TBENCH_FILE_CELL_STUCK} ${ADDITIONAL_LIB_FILES} ${LIB_FILES} ${NETLIST_FILES}
#	cd minrun; vcs -R $(SIMOPTIONS) -sdf min:$(TOP_MODULE):$(SDFMIN) -l $(LOGS_DIR)/vcs/vcs_cell_trans_min.log ${TBENCH_FILE_CELL_TRANS} ${ADDITIONAL_LIB_FILES} ${LIB_FILES} ${NETLIST_FILES}
#	cd minrun; vcs -R $(SIMOPTIONS) -sdf min:$(TOP_MODULE):$(SDFMIN) -l $(LOGS_DIR)/vcs/vcs_dynbr_min.log      ${TBENCH_FILE_DYNBR}      ${ADDITIONAL_LIB_FILES} ${LIB_FILES} ${NETLIST_FILES}
#	cd minrun; vcs -R $(SIMOPTIONS) -sdf min:$(TOP_MODULE):$(SDFMIN) -l $(LOGS_DIR)/vcs/vcs_stabr_min.log      ${TBENCH_FILE_STABR}      ${ADDITIONAL_LIB_FILES} ${LIB_FILES} ${NETLIST_FILES}
#	cd minrun; vcs -R $(SIMOPTIONS) -sdf min:$(TOP_MODULE):$(SDFMIN) -l $(LOGS_DIR)/vcs/vcs_stuck_min.log      ${TBENCH_FILE_STUCK}      ${ADDITIONAL_LIB_FILES} ${LIB_FILES} ${NETLIST_FILES}
#	cd minrun; vcs -R $(SIMOPTIONS) -sdf min:$(TOP_MODULE):$(SDFMIN) -l $(LOGS_DIR)/vcs/vcs_trans_min.log      ${TBENCH_FILE_TRANS}      ${ADDITIONAL_LIB_FILES} ${LIB_FILES} ${NETLIST_FILES}
	date >simmin

sim: simmax simmin 
	mkdir  -p $(LOGS_DIR)/vcs
	@echo "####################################"
	@echo "# SDF Annotation results:          #"
	@echo "####################################"
	grep -i errors $(LOGS_DIR)/vcs/vcs*.log
	@echo "####################################"
	@echo "#Pattern Simulation results:       #"
	@echo "####################################"
	grep -i mismatches $(LOGS_DIR)/vcs/vcs*.log
	date > sim

################################################################################################################
# Reporting/Analyzing 
################################################################################################################
report:
	@for file in `find logs -name "*_pattern.log"` ; do \
	    $(PROJECT_HOME)/scripts/misc/perl/gen_atpg_cov_rpt.pl -p -q -l $$file -r logs/atpg_coverage; \
	done

cov: 
	$(GEN_COV) -l logs/pattern.log | tee -i cov 

gzip: results/$(wildcard results/*.wgl)
	$(WGL_GZIP)
	date > gzip

patch_spf: $(FOLDERS) $(SCAN_PROTOCOL_FILES) $(NONDFT_SIGNAL_FILES) bridge.file slack.file
	cp -rf ../syn/results/nonDFT* stil/.
	#@echo "I_PORB" >> ./stil/nonDFT_in_signals_file.txt
	cp -rf ../syn/results/*.spf stil/.
	$(TMAX) -shell -tcl user_tcl/gen_spf_only.tcl | tee -i logs/$@.log
	rm -rf stil/*.spf stil/*.spf_o stil/*.config
	date > spf

bridge.file: $(BRIDGE_FILE_RM_OUTPUT )
	$(shell ./script/add_asic_shell_hier_to_bridge_file.rb $(BRIDGE_FILE_RM_OUTPUT) > bridge.file)

slack.file: $(SLACK_FILE_RM_OUTPUT )
	$(shell ./script/add_asic_shell_hier_to_slack_report_file.rb $(SLACK_FILE_RM_OUTPUT) > slack.file)

clean:
	rm -rf sim* 
	rm -rf maxrun minrun

clean_all: clean
	rm  -f pattern pattern_syn
	rm -rf logs results reports stil
	rm -rf gzip spf cov bridge.file slack.file

all: bridge.file slack.file spf pattern sim
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

