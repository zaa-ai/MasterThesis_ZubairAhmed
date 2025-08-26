setenv TESTCASE dsi3_pdcm
setenv UVM_TESTCASE top_test
setenv TC_DESCRIPTION "Basic testcase for periodic data collection mode" 
setenv ELAB_OPTIONS "$ELAB_OPTIONS -simprofile=time"
setenv VCS_OPTIONS "$VCS_OPTIONS +uvm_set_type_override=top_default_seq,dsi3_pdcm_seq -Xdprof=timeline -simprofile time"
# do not forget the newline at the end
