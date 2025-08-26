setenv TESTCASE otp_pulse_width
setenv UVM_TESTCASE top_test
setenv TC_DESCRIPTION "OTP pulse width  test" 
setenv VCS_OPTIONS "$VCS_OPTIONS +uvm_set_type_override=top_default_seq,otp_pulse_width_seq"
# do not forget the newline at the end
