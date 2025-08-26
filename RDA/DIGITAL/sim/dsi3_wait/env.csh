setenv TESTCASE dsi3_wait
setenv UVM_TESTCASE top_test
setenv TC_DESCRIPTION "testcase for DSI wait command"
setenv VCS_OPTIONS "$VCS_OPTIONS +uvm_set_type_override=top_default_seq,dsi3_wait_seq"
# do not forget the newline at the end
