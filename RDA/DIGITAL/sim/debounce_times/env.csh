setenv TESTCASE debounce_times
setenv UVM_TESTCASE top_test
setenv TC_DESCRIPTION "testcase for different debounce times"
setenv VCS_OPTIONS "$VCS_OPTIONS +uvm_set_type_override=top_default_seq,debounce_times_seq"
# do not forget the newline at the end
