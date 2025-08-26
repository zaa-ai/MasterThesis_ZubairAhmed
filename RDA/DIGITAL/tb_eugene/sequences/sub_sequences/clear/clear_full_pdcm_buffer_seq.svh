class clear_full_pdcm_buffer_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(clear_full_pdcm_buffer_seq) 
	
	function new(string name = "");
		super.new("clear_full_pdcm_buffer");
	endfunction
	
	virtual task run_tests();
		tdma_scheme_pdcm scheme = new();
		spi_read_pdcm_frame_seq read;
		
		log_sim_description("clear a full data buffer", LOG_LEVEL_SEQUENCE);
		
		// buffer size is 0x3ff (1023)
		// 11 * 93 = 1023
		// 11 * (1 + 2 * (1 + 4*45)) = 1023 
		// -> 11 periods with 2 packets of 180 symbols will fill exactly the buffer
		if(!scheme.randomize() with {packets.size() == 2; symbol_count_min == 180; symbol_count_max == 180; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)
		set_tdma_scheme_pdcm(0, scheme);
		set_tdma_scheme_pdcm(1, scheme);
		
		check_buffer_full(1'b0);
		
		`spi_frame_begin
			`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 8'd11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#(11*scheme.pdcm_period * 1us + 100us);
		
		check_buffer_full(1'b1);
		
		`spi_frame_begin
			`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; pdcm_buffer == 1'b1;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		regmodel.Buffer_IRQs.buffer_interrupt_registers.BUF_IRQ_STAT.DSI_PDCM_FE.write(status, 2'b11); // clear data full IRQ
		#1us;
		
		check_buffer_full(1'b0);
		
		`spi_frame_begin
			`spi_frame_send(read, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		// check results
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			foreach(scheme.packets[packet_index]) begin
				read.expect_empty(2'(channel), packet_index);
			end
		end
		#100us;
	endtask
	
	task check_buffer_full(bit is_full);
		uvm_reg_data_t value;
		logic[project_pkg::DSI_CHANNELS-1:0] expected_value = is_full ? 2'b11 : 2'b00;
		
		if(get_bfwb() == is_full) `uvm_error(this.get_type_name(), $sformatf("Unexpected BFWB pin level, expected %1b, got %1b", !is_full, get_bfwb()))
		
		regmodel.Buffer_IRQs.buffer_interrupt_registers.BUF_FILL_WARN.DSI_PDCM_FW.read(status, value);
		if(2'(value) != expected_value) `uvm_error(this.get_name(), $sformatf("unexpected buffer fill warning value, expected 0b%2b, got 0b%2b", expected_value, value))
		
		regmodel.Buffer_IRQs.buffer_interrupt_registers.BUF_IRQ_STAT.DSI_PDCM_FE.read(status, value);
		if(2'(value) != expected_value) `uvm_error(this.get_name(), $sformatf("unexpected buffer fill error value, expected 0b%2b, got 0b%2b", expected_value, value))
	endtask
endclass