class pdcm_with_maximum_pulse_count_seq extends base_dsi_master_seq;

	`uvm_object_utils(pdcm_with_maximum_pulse_count_seq)
	
	function new(string name = "");
		super.new("pdcm_with_maximum_pulse_count");
	endfunction : new
	
	virtual task run_tests();
		tdma_scheme_pdcm scheme = new();
		log_sim_description("PDCM with maximum pulse count on all channel", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		if(!scheme.randomize() with {packets.size() == 1; symbol_count_min == 4; symbol_count_max == 4; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		
		scheme.packets[0].earliest_start_time = 20;
		scheme.packets[0].latest_start_time = 25;
		scheme.pdcm_period = 100;
		
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)
		set_tdma_scheme_pdcm(0, scheme);
		set_tdma_scheme_pdcm(1, scheme);
	
		`spi_frame_begin
			`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 8'hFF;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#50us;
		registers.check_flag(regmodel.DSI[0].DSI3_channel_registers.DSI_STAT.PULSECNT, 8'hFF);
		registers.check_flag(regmodel.DSI[1].DSI3_channel_registers.DSI_STAT.PULSECNT, 8'hFF);
			
		#('hFF * scheme.pdcm_period * 1us);
		#100us;
		transaction_recorder.expect_tr_count_for_all_channels('hFF);
		
		`spi_frame_begin
			repeat('hFF) begin
				`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11;)
			end
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#100us;
		transaction_recorder.disable_recorder();
	endtask
endclass
