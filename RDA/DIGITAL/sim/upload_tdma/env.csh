setenv TESTCASE upload_tdma
setenv UVM_TESTCASE top_test
setenv TC_DESCRIPTION "testcase for upload of TDMA schemes" 
setenv VCS_OPTIONS "$VCS_OPTIONS +uvm_set_type_override=top_default_seq,upload_tdma_seq"
# do not forget the newline at the end
