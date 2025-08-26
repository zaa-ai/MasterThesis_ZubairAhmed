# We don't wanna have infered Latches so upgrading the warning to an error.
#set_message_info -stop_on -id {ELAB-395}
###################qqq#############################################
# Set the optimization flow to hplp (high performance low power)
set OPTIMIZATION_FLOW "hplp"
source user_tcl/dc_suppress_trivial_project_dependend_warnings.tcl
source $env(PROJECT_HOME)/scripts/misc/tcl/dc_suppress_trivial_messages.tcl
source $env(PROJECT_HOME)/scripts/misc/tcl/procs.tcl

source user_tcl/common_setup.tcl
source $env(PROJECT_HOME)/scripts/syn/tcl/dc/dc_setup_filenames.tcl
source $env(PROJECT_HOME)/scripts/syn/tcl/dc/dc_setup.tcl

#Elmos added
set DCRM_DFT_FINAL_IDDQ_PROTOCOL_OUTPUT_FILE            ${DESIGN_NAME}.mapped.iddq.spf
set DCRM_DFT_FINAL_IDDQ_PATH_REPORT                     ${DESIGN_NAME}.mapped.iddqpath.rpt
set DCRM_DFT_DRC_FINAL_IDDQ_REPORT                      ${DESIGN_NAME}.mapped.dft_drc_inserted.iddq.rpt


read_ddc $RESULTS_DIR/digtop.mapped.ddc


source user_tcl/dc_output_dft.tcl

print_message_info

exit
