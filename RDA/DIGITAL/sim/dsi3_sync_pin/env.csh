setenv TESTCASE dsi3_sync_pin
setenv UVM_TESTCASE top_test
setenv TC_DESCRIPTION "testcase for DSI3 synchronize channels using SYNCB pin" 
setenv VCS_OPTIONS "$VCS_OPTIONS +uvm_set_type_override=top_default_seq,dsi3_sync_pin_seq"
# do not forget the newline at the end
