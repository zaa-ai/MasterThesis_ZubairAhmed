setenv TESTCASE dsi3_quiescent_current
setenv UVM_TESTCASE top_test
setenv TC_DESCRIPTION "Basic testcase for quiescent current measurement" 
setenv VCS_OPTIONS "$VCS_OPTIONS +uvm_set_type_override=top_default_seq,dsi3_iload_seq"
# do not forget the newline at the end
