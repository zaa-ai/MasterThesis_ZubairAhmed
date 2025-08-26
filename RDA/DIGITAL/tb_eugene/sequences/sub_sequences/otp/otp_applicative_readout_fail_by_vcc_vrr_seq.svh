class otp_applicative_readout_fail_by_vcc_vrr_seq extends base_otp_seq;

	`uvm_object_utils(otp_applicative_readout_fail_by_vcc_vrr_seq)
	
	function new(string name = "");
		super.new("otp_applicative_readout_fail_by_vcc_vrr");
	endfunction : new
	
	virtual task run_tests();
		string file_name = "otp_appl_readout_vcc_vrr_fail.dat";
		trimming trimmings[$];
		
		log_sim_description("applicative OTP readout fails by VCC and VRR (REF_FAIL) not ok", LOG_LEVEL_SEQUENCE);
		
		init_trimmings(trimmings);
		write_trimmings(trimmings, file_name);
		reset(file_name);
        #200us;
		registers.check_register(regmodel.OTP_CTRL.OTP_readout_register.OTP_READ_STATUS, 0);
		set_vcc_uv(1'b1);
        get_checker_config().enable_hardware_error_check = 1'b0;
		#200us;	
		check_trimmings(trimmings, BUSY);
		set_vcc_uv(1'b0);
		#200us;
        get_checker_config().enable_hardware_error_check = 1'b1;
		check_trimmings(trimmings, READY);
		
		set_ref_fail(1'b1);
        get_checker_config().enable_hardware_error_check = 1'b0;
		#200us;	
		check_trimmings(trimmings, READY);
		set_ref_fail(1'b0);
		#200us;
        get_checker_config().enable_hardware_error_check = 1'b1;
		check_trimmings(trimmings, READY);
	endtask
endclass