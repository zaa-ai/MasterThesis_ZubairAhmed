class otp_double_bit_ecc_failure_seq extends base_otp_seq;

	`uvm_object_utils(otp_double_bit_ecc_failure_seq)
	
	function new(string name = "");
		super.new("otp_double_bit_ecc_failure");
	endfunction : new
	
	virtual task run_tests();
		spi_read_master_register_seq read_seq;
		string file_name = "otp_double_ecc_failure.dat";
		ecc_otp_writer otp_writer = new();
		address_data_otp_entry entries[$];
		trimming trimmings[$];
		
		log_sim_description("write random values to registers from OTP with double ECC bit failures", LOG_LEVEL_SEQUENCE);
		get_checker_config().enable_hardware_error_check = 1'b0;
		init_trimmings(trimmings);
		
		// initialize all registers with 0
		for (int i = 0; i < trimmings.size(); i++) begin
			otp_writer.add_address_data(16'(trimmings[i].register.get_address()), 16'd0);
		end
		
		for (int i = 0; i < trimmings.size(); i++) begin
			address_data_otp_entry e = new();
			int max_value = trimmings[i].maximum;
			logic[11:0] target_address = 12'(trimmings[i].register.get_address());
			
			if(!e.randomize() with {
					data inside {[0:max_value]}; 
					address == target_address;
					single_bit_address_ecc_failure 	== 1'b0;
					single_bit_data_ecc_failure 	== 1'b0;
					double_bit_address_ecc_failure 	== 1'b0;
					double_bit_data_ecc_failure		== 1'b1;
				}) `uvm_error(this.get_name(), "randomization error")
			
			otp_writer.add_entry(e);
			entries.push_back(e);
		end
		
		otp_writer.write(file_name);
		reset(file_name);
		
		// read registers
		`spi_frame_begin
			`spi_frame_send(read_seq, address == 0; burst_addresses.size() == entries.size(); foreach(burst_addresses[i]) burst_addresses[i] ==  entries[i].address;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		foreach(entries[i]) begin
			if(read_seq.burst_data[i] != 16'd0) `uvm_error(this.get_name(), $sformatf("Read unexpected value in register '%s' at address 0x%4h, expected 0x0000, got 0x%0h", trimmings[i].register.get_name(), entries[i].address, read_seq.burst_data[i]))
		end
		check_otp_fail_irq(1'b1);
	endtask
	
endclass