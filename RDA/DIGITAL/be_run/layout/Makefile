FLOW_CHECK="$(PROJECT_HOME)/scripts/misc/sh/flow_check.sh"
PATCH_NETLIST="$(PROJECT_HOME)/be_run/layout/patch_netlist.csh"
GATE_COUNTER="gate_counter"

ifndef DEBUG
 DEBUG=0
endif
ifndef QUIT
 export QUIT=1
endif

ICC_EXEC = icc_shell -64bit
PNA_OUTPUT_DIR = pna_output

# NXTGRD_FILES
TECH_LIB_PATH = $(shell getPrjCfg.rb -p config/tech)
TCAD_GRD_FILE_MAX = $(shell getPrjCfg.rb -r $(TECH_LIB_PATH) -p tech/phys/extract)
TCAD_GRD_FILE_MIN = $(shell getPrjCfg.rb -r $(TECH_LIB_PATH) -p tech/phys/extract)
#### icc_shell options
OPTIONS = 

##Optional: Specify design library if you want backup step and clean step to use it
##CAUTION: if added, the clean step will delete it
DESIGN_LIB = digtop_LIB

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
	@echo " clean                remove all "
	@echo " clean_all            remove all "
	@echo " ---------------------------------------"
	@echo " ic                   Run whole ICC Flow"
	@echo " ---------------------------------------"
	@echo " *** Stepwise Flow:"
	@echo " init_design_icc      "
	@echo " flat_dp              "
	@echo " place_opt_icc        "
	@echo " clock_opt_ccd_icc    "
	@echo " clock_opt_route_icc  "
	@echo " route_icc            "
	@echo " route_opt_icc        "
	@echo " signoff_drc_icc      "
	@echo " outputs_icc          "
	@echo " "
	@echo " ---------------------------------------"
	@echo " compare netlists with Formality        "
	@echo " ---------------------------------------"
	@echo " compare              "

init_design_icc:
	mkdir -p $(FOLDERS)
	$(ICC_EXEC) $(OPTIONS) -f user_tcl/layout.tcl | tee -i logs/$@.log
	@$(FLOW_CHECK) logs/$@.log $@

flat_dp: init_design_icc
	$(ICC_EXEC) $(OPTIONS) -f user_tcl/layout.tcl | tee -i logs/$@.log
	@$(FLOW_CHECK) logs/$@.log $@

place_opt_icc: init_design_icc
	$(ICC_EXEC) $(OPTIONS) -f user_tcl/layout.tcl | tee -i logs/$@.log
	@$(FLOW_CHECK) logs/$@.log $@

clock_opt_ccd_icc: place_opt_icc
	$(ICC_EXEC) $(OPTIONS) -f user_tcl/layout.tcl | tee -i logs/$@.log
	@$(FLOW_CHECK) logs/$@.log $@

clock_opt_route_icc: clock_opt_ccd_icc
	$(ICC_EXEC) $(OPTIONS) -f user_tcl/layout.tcl | tee -i logs/$@.log
	@$(FLOW_CHECK) logs/$@.log $@

route_icc: clock_opt_route_icc
	$(ICC_EXEC) $(OPTIONS) -f user_tcl/layout.tcl | tee -i logs/$@.log
	@$(FLOW_CHECK) logs/$@.log $@

route_opt_icc: route_icc
	$(ICC_EXEC) $(OPTIONS) -f user_tcl/layout.tcl | tee -i logs/$@.log
	@$(FLOW_CHECK) logs/$@.log $@

chip_finish_icc: route_opt_icc
	$(ICC_EXEC) $(OPTIONS) -f user_tcl/layout.tcl | tee -i logs/$@.log
	@$(FLOW_CHECK) logs/$@.log $@

metal_fill_icc: chip_finish_icc
	$(ICC_EXEC) $(OPTIONS) -f user_tcl/layout.tcl | tee -i logs/$@.log
	@$(FLOW_CHECK) logs/$@.log $@

signoff_drc_icc: metal_fill_icc
	$(ICC_EXEC) $(OPTIONS) -f user_tcl/layout.tcl | tee -i logs/$@.log
	@$(FLOW_CHECK) logs/$@.log $@

outputs_icc: signoff_drc_icc
	$(ICC_EXEC) $(OPTIONS) -f user_tcl/layout.tcl | tee -i logs/$@.log
	#We do not need .spef files written out with ICC, so to not use this files irregulary remove these files
	rm -rf t018lo_1p5m_typical.tluplus_*
	# Patch Netlist for gate level simulation
	@$(PATCH_NETLIST)
	@$(GATE_COUNTER) t7 results/digtop.output.pg.lvs.v | tee reports/gatecount.txt
	@$(FLOW_CHECK) logs/$@.log $@

ic: outputs_icc
	@date > ic

compare:
	fm_shell -f user_tcl/compare.tcl | tee logs/fm.log
	@$(FLOW_CHECK) logs/fm.log $@

#############################################################################################################################
# Utilities Section
#
#############################################################################################################################

## Start icc interactive
icc:
	# $(ICC_EXEC) $(OPTIONS) -gui  -f rm_setup/icc_setup.tcl
	$(ICC_EXEC) $(OPTIONS) -gui  -f user_tcl/layout.tcl

## Start icc interactive and load last valid view
icc_view:
	$(ICC_EXEC) $(OPTIONS) -gui  -f user_tcl/icc_view.tcl

##Backup
BACKUP  = BACKUP.`date "+%m_%d_%H_%M"`
backup:
	rm -rf $(BACKUP)
	mkdir -p $(BACKUP)
	cp -rf $(DESIGN_LIB) reports results logs $(PNA_OUTPUT_DIR) $(BACKUP)

##Clean
clean_all:
	rm  -f init_design_icc flat_dp dp init_design_icc_dp place_opt_icc clock_opt_ccd_icc clock_opt_route_icc route_icc route_opt_icc chip_finish_icc metal_fill_icc signoff_drc_icc outputs_icc ic
	rm -rf $(DESIGN_LIB) logs results/*sbpf* results/*.def results/*pg*  reports/place* reports/clock* reports/route* reports/sign* reports/chip*  *_map\.* \
              net.acts *.attr .zr* Milkyway.cmd.*_*_*_* Milkyway.log.*_*_*_* \.vers* port_mapping.* pna_output
	##ICC_RM-Info: "make clean" does not remove the design library unless you have specified it with the DESIGN_LIB variable in Makefile"
	rm -rf antenna.rule command.log digital_LIB.tf_checker icc_output.txt lc_shell_command.log legalizer_debug_plots skew_opt.tcl snapshot
	rm -rf area.txt digtop_LIB.tf_checker filenames.log fm_shell_command.log formality.log icc_gui.output eco_icc eco
	rm -rf reports signoff_drc_run
clean: clean_all

################################################################################################################
# ICC RM : Eco flow
################################################################################################################
eco_icc:
	$(ICC_EXEC) $(OPTIONS) -f user_tcl/layout.tcl |tee -i logs/$@.log
	@$(PATCH_NETLIST)
	$(FLOW_CHECK) logs/$@.log $@

eco: eco_icc
	date > eco


################################################################################################################
# ICC RM : Focal_opt flow
################################################################################################################
focal_opt_icc: init_folders
	$(ICC_EXEC) $(OPTIONS) -f user_tcl/layout.tcl |tee -i logs/$@.log
	$(FLOW_CHECK) logs/$@.log $@

focal_opt: focal_opt_icc
	date > focal_opt

patch_netlist:
	@$(PATCH_NETLIST)

################################################################################################################
# export all variables to sub processes
################################################################################################################
.EXPORT_ALL_VARIABLES:
