class check_sync_reg_for_pdcm_seq extends dsi3_sync_base_seq;
	
	`uvm_object_utils(check_sync_reg_for_pdcm_seq) 
	
	function new(string name = "");
		super.new("check_sync_reg_for_pdcm");
	endfunction
	
	virtual task run_tests();
		tdma_scheme_pdcm scheme = new();
		log_sim_description("check SYNC register for PDCM", LOG_LEVEL_SEQUENCE);
		
		// disable sync PDCM and TX shift
		registers.write_and_check_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.SYNC_PDCM, 0);
		registers.write_and_check_register(regmodel.DSI_common.common_DSI3_block_registers.DSI_TX_SHIFT, 0);
		
		if(!scheme.randomize() with {packets.size() == 1; symbol_count_max == 16; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		scheme.pdcm_period = 300;
		apply_tdma_scheme(scheme);
		expect_SYNC_IDLE_REG(2'b00, 1'b0);
		
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			expect_SYNC_IDLE_REG(2'b00, 1'b0);
			for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
				expect_SYNC(i, 2'b00, 1'b0);
			end
			
			`spi_frame_begin
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 8'd3;)
				`spi_frame_create(spi_dsi_wait_seq, channel_bits == 2'b01 << channel; wait_time == 15'd300;)
				`spi_frame_create(spi_sync_dsi_channels_seq, external_sync == 1'b0; channel_bits == 2'b11;)
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 8'd3;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
				expect_SYNC(i, 2'b00, 1'b0);
			end
			expect_SYNC_IDLE_REG(2'b11, 1'b0);
			#900us;
			for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
				expect_SYNC(i, i == channel ? 2'b00 : 2'b11, 1'b0);
			end
			expect_SYNC_IDLE_REG(2'b01 << channel, 1'b0);
			#300us;
			for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
				expect_SYNC(i, 2'b00, 1'b0);
			end
			#1500us;
			expect_SYNC_IDLE_REG(2'b00, 1'b0);
		end
	endtask
endclass