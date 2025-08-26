setenv TESTCASE shut_off
setenv UVM_TESTCASE top_test
setenv TC_DESCRIPTION "Testcases for shutting down transceiver e.g. overtemperature, overvoltage and undervoltage" 
setenv VCS_OPTIONS "$VCS_OPTIONS +uvm_set_type_override=top_default_seq,shut_off_seq"
# do not forget the newline at the end
