class otp_random_seq extends base_dsi_master_seq;

	`uvm_object_utils(otp_random_seq)

	function new(string name = "");
		super.new("otp_random");
	endfunction

	virtual task run_tests();
		// disable automatic check for HE flag
		get_checker_config().enable_hardware_error_check = 1'b0;
		log_sim_description("Testcase for random OTP values and trimmings", LOG_LEVEL_TOP);
		
		`create_and_send(otp_random_trimming_seq)
		`create_and_send(otp_write_to_ram_seq)
		`create_and_send(otp_single_bit_ecc_failure_seq)
		`create_and_send(otp_double_bit_ecc_failure_seq)
		`create_and_send(otp_mixed_bit_ecc_failure_seq)
		`create_and_send(otp_applicative_readout_seq)
		`create_and_send(otp_applicative_readout_too_early_seq)
		`create_and_send(otp_applicative_readout_much_too_early_seq)
		`create_and_send(otp_applicative_readout_fail_by_vcc_vrr_seq)
		`create_and_send(otp_applicative_readout_multiple_read_of_same_address_seq)
		`create_and_send(otp_applicative_readout_fail_by_vcc_while_reading_seq)
		`create_and_send(otp_vcc_uv_during_read_seq)
	endtask
endclass
