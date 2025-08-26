setenv TESTCASE dsi3_crm_ecc_2_bit_error
setenv UVM_TESTCASE top_test
setenv TC_DESCRIPTION "Basic testcase for command response mode with 2 bit failures in datapath" 
setenv VCS_OPTIONS "$VCS_OPTIONS +uvm_set_type_override=top_default_seq,dsi3_crm_ecc_2_bit_error_seq"
# do not forget the newline at the end
