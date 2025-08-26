# ELMOS: write out lbist test protocol and netlist for generating the required seed
#        write out lbist testbench to check signature

#############################################################################
# Write out LBIST Test Protocols and Design
#############################################################################

change_names -rules verilog -hierarchy

write_test_protocol   -test_mode LBIST -output ${RESULTS_DIR}/${DCRM_DFT_LBIST_PROTOCOL_FILE}

write -format verilog -hier            -output ${RESULTS_DIR}/${DCRM_LBIST_VERILOG_FILE}
write -format ddc     -hier            -output ${RESULTS_DIR}/${DCRM_LBIST_DDC_FILE}

write_test -format stil -output ${RESULTS_DIR}/bist_tb
sh stil2verilog ${RESULTS_DIR}/bist_tb.stil ${RESULTS_DIR}/bist_tb -replace
