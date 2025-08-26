setenv TESTCASE register_access
setenv UVM_TESTCASE top_test
setenv TC_DESCRIPTION "testcase for master register access" 
setenv VCS_OPTIONS "$VCS_OPTIONS +uvm_set_type_override=top_default_seq,register_access_seq"
# do not forget the newline at the end
