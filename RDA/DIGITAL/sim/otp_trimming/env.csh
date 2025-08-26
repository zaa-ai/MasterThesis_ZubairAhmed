setenv TESTCASE otp_trimming
setenv UVM_TESTCASE top_test
setenv TC_DESCRIPTION "OTP Trimming test" 
setenv VCS_OPTIONS "$VCS_OPTIONS +uvm_set_type_override=top_default_seq,otp_trimming_seq"
# do not forget the newline at the end
