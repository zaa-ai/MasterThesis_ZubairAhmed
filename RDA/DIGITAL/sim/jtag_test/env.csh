setenv TESTCASE jtag_test
setenv UVM_TESTCASE top_test
setenv TC_DESCRIPTION "Basic testcase for JTAG and test" 
setenv VCS_OPTIONS "$VCS_OPTIONS +uvm_set_type_override=top_default_seq,jtag_test_seq"
# do not forget the newline at the end
