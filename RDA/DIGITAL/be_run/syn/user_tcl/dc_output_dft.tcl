#############################################################################
# DFT Write out Test Protocols and Reports
#############################################################################

# write_scan_def adds SCANDEF information to the design database in memory, so 
# this command must be performed prior to writing out the design database 
# containing binary SCANDEF.
#Elmos added
set DCRM_DFT_FINAL_IDDQ_PROTOCOL_OUTPUT_FILE            ${DESIGN_NAME}.mapped.iddq.spf
set DCRM_DFT_FINAL_IDDQ_PATH_REPORT                     ${DESIGN_NAME}.mapped.iddqpath.rpt
set DCRM_DFT_DRC_FINAL_IDDQ_REPORT                      ${DESIGN_NAME}.mapped.dft_drc_inserted.iddq.rpt

set_dft_drc_rules -allow  {TEST-504 TEST-505}

write_test_model -format ctl -output ${RESULTS_DIR}/${DCRM_DFT_FINAL_CTL_OUTPUT_FILE}

report_dft_signal > ${REPORTS_DIR}/${DCRM_DFT_FINAL_DFT_SIGNALS_REPORT}

#read_test_protocol -section test_setup -test_mode Iddq_mode            ctl/digtop.atpg_iddq_init.ctl  

# DFT outputs for compressed scan mode
# If you have defined you own test modes, change the name of the test mode from 
# "ScanCompression_mode" to the one that you have specified using define_test_mode command.
current_test_mode ScanCompression_mode
read_test_protocol -section test_setup -test_mode ScanCompression_mode ctl/digtop.atpg_compr_init.ctl 
set_dft_drc_configuration -internal_pins disable
write_test_protocol -test_mode ScanCompression_mode -output ${RESULTS_DIR}/${DCRM_DFT_FINAL_SCAN_COMPR_PROTOCOL_OUTPUT_FILE}
report_scan_path > ${REPORTS_DIR}/${DCRM_DFT_FINAL_SCAN_COMPR_SCAN_PATH_REPORT}
dft_drc 
dft_drc -verbose > ${REPORTS_DIR}/${DCRM_DFT_DRC_FINAL_SCAN_COMPR_REPORT}

# DFT outputs for Internal_Scan
current_test_mode Internal_scan
read_test_protocol -section test_setup -test_mode Internal_scan        ctl/digtop.atpg_std_init.ctl  
set_dft_drc_configuration -internal_pins disable
write_test_protocol -test_mode Internal_scan -output ${RESULTS_DIR}/${DCRM_DFT_FINAL_PROTOCOL_OUTPUT_FILE}
report_scan_path > ${REPORTS_DIR}/${DCRM_DFT_FINAL_SCAN_PATH_REPORT}
dft_drc
dft_drc -verbose -coverage_estimate > ${REPORTS_DIR}/${DCRM_DFT_DRC_FINAL_REPORT}

#return -level 2
# DFT outputs for standard iddq mode
current_test_mode Internal_scan
read_test_protocol -section test_setup -test_mode Internal_scan        ctl/digtop.atpg_iddq_init.ctl -overwrite
set_dft_drc_configuration -internal_pins disable
write_test_protocol -test_mode Internal_scan -output ${RESULTS_DIR}/${DCRM_DFT_FINAL_IDDQ_PROTOCOL_OUTPUT_FILE}
report_scan_path > ${REPORTS_DIR}/${DCRM_DFT_FINAL_IDDQ_PATH_REPORT}
dft_drc 
dft_drc -verbose -coverage_estimate > ${REPORTS_DIR}/${DCRM_DFT_DRC_FINAL_IDDQ_REPORT}


write_scan_def -output ${RESULTS_DIR}/${DCRM_DFT_FINAL_SCANDEF_OUTPUT_FILE}
check_scan_def > ${REPORTS_DIR}/${DCRM_DFT_FINAL_CHECK_SCAN_DEF_REPORT}

