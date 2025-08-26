setenv TESTCASE dsi3_crc
setenv UVM_TESTCASE top_test
setenv TC_DESCRIPTION "Basic testcase for PDCM/CRM with different CRC settings" 
setenv ELAB_OPTIONS "$ELAB_OPTIONS -simprofile=time"
setenv VCS_OPTIONS "$VCS_OPTIONS +uvm_set_type_override=top_default_seq,dsi3_crc_seq -Xdprof=timeline -simprofile time"
# do not forget the newline at the end
