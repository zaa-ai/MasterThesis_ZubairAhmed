setenv TESTCASE dsi3_crm_timing
setenv UVM_TESTCASE top_test
setenv TC_DESCRIPTION "testcase to measure CRM answer timings" 
setenv VCS_OPTIONS "$VCS_OPTIONS +uvm_set_type_override=top_default_seq,dsi3_crm_timing_seq"
# do not forget the newline at the end
