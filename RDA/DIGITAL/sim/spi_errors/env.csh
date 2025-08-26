setenv TESTCASE spi_errors
setenv UVM_TESTCASE top_test
setenv TC_DESCRIPTION "Testcases for different kinds of SPI errors e.g. wrong CRC, incomplete commands, invalid commands, ..." 
setenv VCS_OPTIONS "$VCS_OPTIONS +uvm_set_type_override=top_default_seq,spi_errors_seq"
# do not forget the newline at the end
