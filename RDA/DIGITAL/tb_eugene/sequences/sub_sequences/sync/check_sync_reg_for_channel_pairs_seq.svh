class check_sync_reg_for_channel_pairs_seq extends dsi3_sync_base_seq;
	
	`uvm_object_utils(check_sync_reg_for_channel_pairs_seq) 
	
	function new(string name = "");
		super.new("check_sync_reg_for_channel_pairs");
	endfunction
	
	virtual task run_tests();
		tdma_scheme_pdcm scheme = new();
		log_sim_description("check SYNC register for channel pairs", LOG_LEVEL_SEQUENCE);
		
		if(!scheme.randomize() with {packets.size() == 1; symbol_count_min == 4; symbol_count_max == 4; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		scheme.pdcm_period = 133;
		apply_tdma_scheme(scheme);
		
		expect_SYNC_IDLE_REG(2'b00, 1'b0);
		for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
			expect_SYNC(i, 2'b00, 1'b0);
		end
		
		`spi_frame_begin
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b01; broad_cast == 1'b0;)
			`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b10; pulse_count == 8'd3;)
			`spi_frame_create(spi_dsi_wait_seq, channel_bits == 2'b01; wait_time == 15'd300;)
			`spi_frame_create(spi_dsi_wait_seq, channel_bits == 2'b10; wait_time == 15'd300;)
			`spi_frame_create(spi_sync_dsi_channels_seq, external_sync == 1'b0; channel_bits == 2'b11;)
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b10; broad_cast == 1'b0;)
			`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b01; pulse_count == 8'd3;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		#100us;
		expect_SYNC_IDLE_REG(2'b11, 1'b0);
		for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
			expect_SYNC(i, 2'b00, 1'b0);
		end
		#300us;
		expect_SYNC_IDLE_REG(2'b11, 1'b0);
		expect_SYNC(0, 2'b00, 1'b0);
		expect_SYNC(1, 2'b00, 1'b0);
		#250us;
		for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
			expect_SYNC(i, 2'b00, 1'b0);
		end
		#550us;
		expect_SYNC_IDLE_REG(2'b00, 1'b0);
	endtask
endclass