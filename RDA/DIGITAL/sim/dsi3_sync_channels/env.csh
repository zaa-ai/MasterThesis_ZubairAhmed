setenv TESTCASE dsi3_sync_channels
setenv UVM_TESTCASE top_test
setenv TC_DESCRIPTION "testcase for DSI3 synchronize channels command" 
setenv VCS_OPTIONS "$VCS_OPTIONS +uvm_set_type_override=top_default_seq,dsi3_sync_channels_seq"
# do not forget the newline at the end
