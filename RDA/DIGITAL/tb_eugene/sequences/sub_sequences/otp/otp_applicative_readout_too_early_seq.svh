class otp_applicative_readout_too_early_seq extends base_otp_seq;

	`uvm_object_utils(otp_applicative_readout_too_early_seq)
	
	function new(string name = "");
		super.new("otp_applicative_readout_too_early");
	endfunction : new
	
	virtual task run_tests();
		string file_name = "otp_appl_readout_too_early.dat";
		trimming trimmings[$];
		
		log_sim_description("applicative OTP readout before RFC", LOG_LEVEL_SEQUENCE);
		
		init_trimmings(trimmings);
		write_trimmings(trimmings, file_name);
		
		read_otp(file_name);
		set_resb(0);
		#100us;
		set_resb(1); 
		#200us;
        get_checker_config().enable_hardware_error_check = 1'b0;
		
		for (int otp_index = 0; otp_index < 10; otp_index++) begin
			check_trimming_not_readable(otp_index);
		end
		#1ms;
        `spi_frame_begin
        `spi_frame_create(spi_reset_seq,)
        `spi_frame_end
		check_trimmings(trimmings, READY);
        get_checker_config().enable_hardware_error_check = 1'b1;
	endtask
	
	task check_trimming_not_readable(int otp_index);
		spi_read_master_register_seq read_seq;

        get_checker_config().enable_mirroring_check = 1'b0;
		regmodel.OTP_CTRL.OTP_readout_register.OTP_READ_ADDRESS.write(status, otp_index);
        get_checker_config().enable_mirroring_check = 1'b1;
		#200ns;
		
		// re-read OTP_READ_ADDRESS -> must not be writable
		`spi_frame_begin
            `spi_frame_create(spi_reset_seq,)
			`spi_frame_send(read_seq, address == 12'(addresses_pkg::ADDR_OTP_CTRL_OTP_READ_ADDRESS); burst_addresses.size() == 0; )
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end_with_status({HE, SCI, NT0, NT1})
		if(read_seq.data != 16'h0) `uvm_error(this.get_name(), $sformatf("Read unexpected OTP_READ_ADDRESS value, expected 0x0000, got 0x%0h", read_seq.data))	
		#200ns;
		
		// read OTP_READ_STATUS
		`spi_frame_begin
			`spi_frame_send(read_seq, address == 12'(addresses_pkg::ADDR_OTP_CTRL_OTP_READ_STATUS); burst_addresses.size() == 0; )
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end_with_status({HE, SCI, NT0, NT1}) // SCI cannot be removed since it conatins an interrupt which can only be deleted by a write access not possible in this state
		if(otp_read_status_t'(read_seq.data) != INITIAL) `uvm_error(this.get_name(), $sformatf("Read unexpected READ STATUS value at OTP index %0d, expected 0x%0h, got 0x%0h", otp_index, INITIAL, read_seq.data))
	endtask
endclass