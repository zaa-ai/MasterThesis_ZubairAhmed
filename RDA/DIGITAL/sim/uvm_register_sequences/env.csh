setenv TESTCASE uvm_register_sequences
setenv UVM_TESTCASE top_test
setenv TC_DESCRIPTION "testcase that runs all UVM register sequences" 
setenv VCS_OPTIONS "$VCS_OPTIONS +uvm_set_type_override=top_default_seq,uvm_register_sequences_seq"
# do not forget the newline at the end
