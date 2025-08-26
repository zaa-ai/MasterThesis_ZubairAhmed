setenv TESTCASE dsi3_sync_shift
setenv UVM_TESTCASE top_test
setenv TC_DESCRIPTION "Basic testcase for syncing and shifting" 
setenv ELAB_OPTIONS "$ELAB_OPTIONS"
setenv VCS_OPTIONS "$VCS_OPTIONS +uvm_set_type_override=top_default_seq,dsi3_sync_shift_seq"
# do not forget the newline at the end
