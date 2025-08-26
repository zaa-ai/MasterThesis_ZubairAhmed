setenv TESTCASE interrupts_test
setenv UVM_TESTCASE top_test
setenv TC_DESCRIPTION "Test all interrupts" 
setenv VCS_OPTIONS "$VCS_OPTIONS +uvm_set_type_override=top_default_seq,interrupts_seq"
# do not forget the newline at the end
