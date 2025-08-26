setenv TESTCASE appl_examples_in_spec
setenv UVM_TESTCASE top_test
setenv TC_DESCRIPTION "Simulate the application examples described in the specification." 
setenv VCS_OPTIONS "$VCS_OPTIONS +uvm_set_type_override=top_default_seq,appl_examples_in_spec_seq"
# do not forget the newline at the end
