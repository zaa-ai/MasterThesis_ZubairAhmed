if {$env(WRAPPER) ne ""} {
add_nofaults asic_inst/xdigtop/i_logic_top/i_test/i_test_control/U_decompressor_ScanCompression_mode
add_nofaults asic_inst/xdigtop/i_logic_top/i_test/i_test_control/U_compressor_ScanCompression_mode
} else {
add_nofaults i_logic_top/i_test/i_test_control/U_decompressor_ScanCompression_mode
add_nofaults i_logic_top/i_test/i_test_control/U_compressor_ScanCompression_mode
}

if { $env(DIFF) eq "0" } {
    if { $PATTERN_NAME eq "dynbr" || $PATTERN_NAME eq "stabr" } {
	add_faults -node_file ${NODE_FILE}
    } elseif { $PATTERN_NAME eq "cell_trans" || $PATTERN_NAME eq "cell_stuck" } {
	add_faults -all -cell_aware
    } else {
	add_faults -all
    }
} else {
    puts "RM-Info: Reading faults \"${RESULTS_DIR}/${DESIGN_NAME}_${PATTERN_NAME}_post.comp.faults.gz\""
    read_faults ${RESULTS_DIR}/${DESIGN_NAME}_${PATTERN_NAME}_post.comp.faults.gz -retain
    update_faults -reset_au

    set LIMIT_DB_ATPG           "10"
    set LIMIT_TD_ATPG           "10"
    set LIMIT_TD_SLACK_ATPG     "10"
    set LIMIT_CT_ATPG           "10"
    set LIMIT_CT_SLACK_ATPG     "10"
    set LIMIT_SB_ATPG           "10"
    set LIMIT_SA_ATPG           "10"
    set LIMIT_CS_ATPG           "10"
    set LIMIT_ID_ATPG           "10"
}
