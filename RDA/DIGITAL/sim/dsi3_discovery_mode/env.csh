setenv TESTCASE dsi3_discovery_mode
setenv UVM_TESTCASE top_test
setenv TC_DESCRIPTION "Basic testcase for discovery mode" 
setenv VCS_OPTIONS "$VCS_OPTIONS +uvm_set_type_override=top_default_seq,dsi3_discovery_mode_seq"
# do not forget the newline at the end
