class otp_write_to_ram_seq extends base_otp_seq;

	`uvm_object_utils(otp_write_to_ram_seq)
	
	function new(string name = "");
		super.new("otp_write_to_ram");
	endfunction : new
	
	virtual task run_tests();
		random_trimming trimmings[$];
		spi_read_master_register_seq read_seq;
		string file_name = "otp_random_ram.dat";
		ecc_otp_writer otp_writer = new();
		
		log_sim_description("write random values to RAM from OTP", LOG_LEVEL_SEQUENCE);
		
		for (int ram_adr = int'(project_pkg::BASE_ADDR_RAM); ram_adr< int'(project_pkg::BASE_ADDR_RAM + project_pkg::SIZE_RAM); ram_adr++) begin
			random_trimming trim = new();
			if(!trim.randomize() with {address == 12'(ram_adr);}) `uvm_error(this.get_name(), "randomization error")
			trimmings.push_back(trim);
			otp_writer.add_address_data(trim.address, trim.data);	
		end
		otp_writer.write(file_name);
		reset(file_name);
			
		// read RAM
		`spi_frame_begin
			`spi_frame_send(read_seq, address == 0; burst_addresses.size() == int'(project_pkg::SIZE_RAM); foreach(burst_addresses[i]) burst_addresses[i] ==  trimmings[i].address; )
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		foreach(trimmings[i]) begin
			if(read_seq.burst_data[i] != 16'd0) `uvm_error(this.get_name(), $sformatf("Read unexpected value in RAM index %0d at address 0x%4h, expected 0x0000, got 0x%0h", i, project_pkg::BASE_ADDR_RAM+i, read_seq.burst_data[i]))
		end
	endtask
endclass