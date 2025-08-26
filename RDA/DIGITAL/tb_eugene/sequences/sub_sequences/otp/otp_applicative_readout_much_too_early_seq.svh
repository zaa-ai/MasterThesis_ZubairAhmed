class otp_applicative_readout_much_too_early_seq extends base_otp_seq;

	`uvm_object_utils(otp_applicative_readout_much_too_early_seq)
	
	function new(string name = "");
		super.new("otp_applicative_readout_much_too_early");
	endfunction : new
	
	virtual task run_tests();
		string file_name = "otp_appl_readout_much_too_early.dat";
		trimming trimmings[$];
		
		log_sim_description("applicative OTP readout before RFC and before OTP/RAM init", LOG_LEVEL_SEQUENCE);
		
		init_trimmings(trimmings);
		write_trimmings(trimmings, file_name);
		
		read_otp(file_name);
		set_resb(0);
		#100us;
		set_resb(1);
		#100us;
        get_checker_config().enable_hardware_error_check = 1'b0;
		check_trimmings(trimmings, FAIL, 1);
		#1ms;
		check_trimmings(trimmings, READY);
        get_checker_config().enable_hardware_error_check = 1'b1;
	endtask
endclass