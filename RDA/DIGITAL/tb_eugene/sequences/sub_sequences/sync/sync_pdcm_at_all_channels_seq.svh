class sync_pdcm_at_all_channels_seq extends dsi3_sync_base_seq;
	
	`uvm_object_utils(sync_pdcm_at_all_channels_seq) 
	
	function new(string name = "");
		super.new("sync_pdcm_at_all_channels");
	endfunction
	
	virtual task run_tests();
		time spi_end;
		tdma_scheme_pdcm scheme_ch1 = new();
		tdma_scheme_pdcm scheme_ch2 = new();
		
		log_sim_description("synchronize PDCM at all channels", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		if(!scheme_ch1.randomize() with {packets.size() inside {[1:5]}; symbol_count_max == 8; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		if(!scheme_ch2.randomize() with {packets.size() inside {[1:5]}; symbol_count_max == 8; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		
		registers.write_and_check_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.SYNC_PDCM, 0);
		registers.write_and_check_register(regmodel.DSI_common.common_DSI3_block_registers.DSI_TX_SHIFT, 0);
		
		`upload_tdma_scheme_with(scheme_ch1, channels == 2'b01;)
		`upload_tdma_scheme_with(scheme_ch2, channels == 2'b10;)
		set_tdma_scheme_pdcm(0, scheme_ch1);
		set_tdma_scheme_pdcm(0, scheme_ch2);
		
		`spi_frame_begin
			`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b01; pulse_count == 1;)
			`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b10; pulse_count == 2;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#50us;
		`spi_frame_begin
			`spi_frame_create(spi_sync_dsi_channels_seq, external_sync == 1'b0; channel_bits == 2'b11;)
			`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b01; pulse_count == 1;)
			`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b10; pulse_count == 1;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		spi_end = $time;

		#(3 * scheme_ch2.pdcm_period * 1us);
		#1ms;
		
		check_channel_sync(2'b11, 2'b11, spi_end);
		transaction_recorder.clear_all();
	endtask
endclass