class pdcm_sync_with_different_tdma_schemes_seq extends dsi3_sync_base_seq;
	
	`uvm_object_utils(pdcm_sync_with_different_tdma_schemes_seq) 
	
	function new(string name = "");
		super.new("pdcm_sync_with_different_tdma_schemes");
	endfunction

	virtual task run_tests();
		tdma_scheme_pdcm scheme_0 = new();
		tdma_scheme_pdcm scheme_1 = new();
		
		log_sim_description("sync PDCM with SYNC_PDCM == 1 and different TDMA schemes", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		if(!scheme_0.randomize() with {packets.size() == 1; symbol_count_min == 8; symbol_count_max == 8; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		if(!scheme_1.randomize() with {packets.size() == 1; symbol_count_min == 8; symbol_count_max == 8; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		scheme_0.pdcm_period = 300;
		scheme_1.pdcm_period = 400;

		`upload_tdma_scheme_with(scheme_0, channels == 2'b01;)
		`upload_tdma_scheme_with(scheme_1, channels == 2'b10;)
		set_tdma_scheme_pdcm(0, scheme_0);
		set_tdma_scheme_pdcm(1, scheme_1);
		#50us;
		
		regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.SYNC_PDCM.write(status, 1'b1);

		`spi_frame_begin
			`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b01; pulse_count == 5;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#100us;
		`spi_frame_begin
			`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b10; pulse_count == 5;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		#(6 * scheme_1.pdcm_period * 1us);
		
		transaction_recorder.expect_tr_count_for_all_channels(5);
		#100us;
		transaction_recorder.disable_recorder();
	endtask
endclass