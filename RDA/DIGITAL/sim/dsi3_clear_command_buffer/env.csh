setenv TESTCASE dsi3_clear_command_buffer
setenv UVM_TESTCASE top_test
setenv TC_DESCRIPTION "Basic testcase for clearing DSI command buffer" 
setenv VCS_OPTIONS "$VCS_OPTIONS +uvm_set_type_override=top_default_seq,dsi3_clear_command_buffer_seq"
# do not forget the newline at the end
