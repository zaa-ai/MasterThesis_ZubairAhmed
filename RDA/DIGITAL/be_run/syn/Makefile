FLOW_CHECK="$(PROJECT_HOME)/scripts/misc/sh/flow_check.sh"
FF_WO_RESET_CHECK="$(PROJECT_HOME)/scripts/misc/perl/get_ff_wo_reset.pl"

ifndef DEBUG
 DEBUG=0
endif
ifndef QUIT
 export QUIT=1
endif

DC_EXEC = dcnxt_shell

#### dc_shell options
OPTIONS = -64bit -topographical_mode

THIS_TARGET = $@

FOLDERS = logs results reports

help:
	@echo " "
	@echo " Makefile help"
	@echo " ============="
	@echo " "
	@echo " usage: make TARGET "
	@echo " "
	@echo " *** TARGET:"
	@echo " "
	@echo " ---------------------------------------"
	@echo " Clean-Up "
	@echo " ---------------------------------------"
	@echo " clean        remove all non-used files"
	@echo "              (results, reports and logs are kept)"
	@echo " clean_all    remove all"
	@echo " "
	@echo " ---------------------------------------"
	@echo " Synthesis "
	@echo " ---------------------------------------"
	@echo " syn "
	@echo " "
	@echo " ---------------------------------------"
	@echo " Compare netlists  vs. RTL with Formality"
	@echo " ---------------------------------------"
	@echo " compare "

syn: syn
	mkdir -p $(FOLDERS)
	$(DC_EXEC) $(OPTIONS) -f user_tcl/syn.tcl | tee logs/dc.log
	@$(FLOW_CHECK) logs/dc.log $@
	${MAKE} postsyn clean

output_dft:
	$(DC_EXEC) $(OPTIONS) -f user_tcl/syn_output.tcl | tee logs/dc_output_dft.log
	@$(FLOW_CHECK) logs/dc_output_dft.log $@
		
postsyn:
	perl $(FF_WO_RESET_CHECK) logs/dc.log > logs/additional_checks.log

compare:
# for formal verification we want to analyze the original CELLS files
	sed -i -e '/START FM SCRIPT/,/END FM SCRIPT/s#/CELLS/hdl/#/CELLS/fv/#' results/digtop.autoread_rtl.tcl
	fm_shell -f user_tcl/compare.tcl | tee logs/fm.log
	${MAKE} clean

clean:
	rm -rf command.log filenames*.log WORK_autoread digtop_LIB *_autoread 
	rm -rf fm_shell_command*.log fm_shell_command*.lck formality*.log formality*.lck formality*_svf FM_WORK*
	rm -rf lc_shell_command.log syn output_dft udul_default_fin.log* 

clean_all: clean
	rm -rf reports/* results/* logs/* command.log .DC_log_snapshot* default.* __tmp_tf__.*

################################################################################################################
# Start dc interactive
################################################################################################################
dci:
	dc_shell -64bit -topographical_mode -f user_tcl/dc_interactive.tcl

################################################################################################################
# export all variables to sub processes
################################################################################################################
.EXPORT_ALL_VARIABLES:
