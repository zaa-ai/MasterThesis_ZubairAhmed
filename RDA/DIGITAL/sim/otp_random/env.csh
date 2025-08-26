setenv TESTCASE otp_random
setenv UVM_TESTCASE top_test
setenv TC_DESCRIPTION "testcase for random OTP and trimmings"
setenv VCS_OPTIONS "$VCS_OPTIONS +uvm_set_type_override=top_default_seq,otp_random_seq"
# do not forget the newline at the end
