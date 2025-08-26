setenv TESTCASE ic_startup
setenv UVM_TESTCASE top_test
setenv TC_DESCRIPTION "testcase for IC startup procedure"
setenv VCS_OPTIONS "$VCS_OPTIONS +uvm_set_type_override=top_default_seq,ic_startup_seq"
# do not forget the newline at the end
