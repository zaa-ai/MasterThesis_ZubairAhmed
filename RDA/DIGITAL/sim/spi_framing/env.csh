setenv TESTCASE spi_framing
setenv UVM_TESTCASE top_test
setenv TC_DESCRIPTION "Testcases for different types of SPI framing (different CSB handlings)" 
setenv VCS_OPTIONS "$VCS_OPTIONS +uvm_set_type_override=top_default_seq,spi_framing_seq"
# do not forget the newline at the end
