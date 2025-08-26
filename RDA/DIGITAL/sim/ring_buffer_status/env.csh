setenv TESTCASE ring_buffer_status
setenv UVM_TESTCASE top_test
setenv TC_DESCRIPTION "testcase for ring Buffer" 
setenv VCS_OPTIONS "$VCS_OPTIONS +uvm_set_type_override=top_default_seq,ring_buffer_status_seq"
# do not forget the newline at the end
