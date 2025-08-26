setenv TESTCASE ic_status_word
setenv UVM_TESTCASE top_test
setenv TC_DESCRIPTION "testcase for IC status word"
setenv VCS_OPTIONS "$VCS_OPTIONS +uvm_set_type_override=top_default_seq,ic_status_word_seq"
# do not forget the newline at the end
