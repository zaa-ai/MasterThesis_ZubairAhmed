setenv TESTCASE dsi3_clear_data_buffer
setenv UVM_TESTCASE top_test
setenv TC_DESCRIPTION "testcase for clearing data buffer" 
setenv VCS_OPTIONS "$VCS_OPTIONS +uvm_set_type_override=top_default_seq,dsi3_clear_data_buffer_seq"
# do not forget the newline at the end
