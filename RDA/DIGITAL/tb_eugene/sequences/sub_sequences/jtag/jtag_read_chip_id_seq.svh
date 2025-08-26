class jtag_read_chip_id_seq extends base_dsi_master_seq;

	rand logic[15:0] chip_id_low;
	rand logic[15:0] chip_id_high;

	`uvm_object_utils(jtag_read_chip_id_seq) 
    
	function new(string name = "");
		super.new("jtag_read_chip_id");
	endfunction : new

	virtual task run_tests();
		log_sim_description("read chip ID", LOG_LEVEL_SEQUENCE);
		
		init_otp();
		read_chip_id_using_spi();
		read_chip_id_using_jtag();
		#100us;
	endtask
	
	task read_chip_id_using_spi();
		spi_read_master_register_seq read_seq;
		
		log_sim_description("read chip ID using SPI burst read", LOG_LEVEL_SEQUENCE);
		`spi_frame_begin
			`spi_frame_send(read_seq, address == 12'(ADDR_INFO_CHIP_ID_HIGH); burst_addresses.size() == 1; burst_addresses[0] == 12'(ADDR_INFO_CHIP_ID_LOW);)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end 
	
		`uvm_info(get_type_name(), $sformatf("chip ID using SPI burst read: CHIP_ID_LOW = 0x%04h, CHIP_ID_HIGH = 0x%04h", read_seq.burst_data[0], read_seq.data), UVM_MEDIUM)		
		if(read_seq.burst_data[0] != chip_id_low) `uvm_error(get_type_name(), $sformatf("read unexpected value for CHIP_ID_LOW using SPI, expected 0x%04h, got 0x%04h", chip_id_low, read_seq.burst_data[0]))
		if(read_seq.data != chip_id_high) `uvm_error(get_type_name(), $sformatf("read unexpected value for CHIP_ID_HIGH using SPI, expected 0x%04h, got 0x%04h", chip_id_high, read_seq.data))
	endtask
	
	task read_chip_id_using_jtag();
		jtag_read_elip_seq read_low_seq;
		jtag_read_incr_elip_seq read_high_seq; 
		log_sim_description("read chip ID using JTAG incremental read", LOG_LEVEL_SEQUENCE);
		
		jtag_enable_with_tdo(1'b1);
		
		`uvm_do_on_with( read_low_seq, m_jtag_master_agent.m_sequencer, {init == 1; address == ADDR_INFO_CHIP_ID_LOW;})
		`uvm_do_on_with(read_high_seq, m_jtag_master_agent.m_sequencer, {init == 0;})
		`uvm_do_on_with(read_high_seq, m_jtag_master_agent.m_sequencer, {init == 0;})
		
		`uvm_info(get_type_name(), $sformatf("chip ID using JTAG incremental read: CHIP_ID_LOW = 0x%04h, CHIP_ID_HIGH = 0x%04h", read_low_seq.read_value, read_high_seq.read_value), UVM_MEDIUM)		
		if(16'(read_low_seq.read_value) != chip_id_low) `uvm_error(get_type_name(), $sformatf("read unexpected value for CHIP_ID_LOW using JTAG, expected 0x%04h, got 0x%04h", chip_id_low, read_low_seq.read_value))
		if(16'(read_high_seq.read_value) != chip_id_high) `uvm_error(get_type_name(), $sformatf("read unexpected value for CHIP_ID_HIGH using JTAG, expected 0x%04h, got 0x%04h", chip_id_high, read_high_seq.read_value))
	endtask
	
	task init_otp();
		string file_name = "otp_chip_id.dat";
		ecc_otp_writer otp_writer = new();
		otp_writer.add_address_data(ADDR_TIMEBASE_TRIM_OSC, 16'h004B);	
		otp_writer.add_address_data(ADDR_TIMEBASE_TRIM_OSC_TCF, 16'h0003);
		otp_writer.add_address_data(ADDR_INFO_CHIP_ID_LOW, chip_id_low);
		otp_writer.add_address_data(ADDR_INFO_CHIP_ID_HIGH, chip_id_high);
		
		otp_writer.write(file_name);
		reset(file_name);
		#100us;
	endtask
	
endclass

