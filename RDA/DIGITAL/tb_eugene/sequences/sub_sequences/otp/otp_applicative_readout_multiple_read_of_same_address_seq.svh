class otp_applicative_readout_multiple_read_of_same_address_seq extends base_otp_seq;

	`uvm_object_utils(otp_applicative_readout_multiple_read_of_same_address_seq)
	
	function new(string name = "");
		super.new("otp_applicative_readout_multiple_read_of_same_address");
	endfunction : new
	
	virtual task run_tests();
		string file_name = "otp_appl_readout_same_address.dat";
		trimming trimmings[$];
		
		log_sim_description("applicative OTP readout with multiple reads of same address", LOG_LEVEL_SEQUENCE);
		
		init_trimmings(trimmings);
		write_trimmings(trimmings, file_name);
		reset(file_name);
		
        get_checker_config().enable_hardware_error_check = 1'b0;
		foreach(trimmings[i]) begin
			uvm_reg_addr_t address = trimmings[i].register.get_address();
			repeat(3) check_trimming(i*4, address[15:8], READY);
        end
        get_checker_config().enable_hardware_error_check = 1'b1;
	endtask
endclass