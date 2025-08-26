class pdcm_receive_packet_with_more_than_255_symbols_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(pdcm_receive_packet_with_more_than_255_symbols_seq)

	function new(string name = "");
		super.new("pdcm_receive_packet_with_more_than_255_symbols");
	endfunction
	
	task run_tests();
		int start_symbol_count = 255;
		int end_symbol_count = 260;
		tdma_scheme_pdcm scheme = new();
			
		log_sim_description("receive packets with more than 255 symbols", LOG_LEVEL_SEQUENCE);
		
		if(!scheme.randomize() with {packets.size() == 1; symbol_count_min == 255; symbol_count_max == 255; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		scheme.pdcm_period = scheme.pdcm_period + 100; 
		
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)
		
		for(int symbol_count = start_symbol_count; symbol_count < end_symbol_count; symbol_count++) begin
			for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
				
				log_sim_description($sformatf("receive %0d symbols at channel %0d", symbol_count, channel));
				scheme.packets[0].symbol_count = symbol_count;
				set_tdma_scheme_pdcm(channel, scheme);
				
				`spi_frame_begin
					`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b01 << channel; pulse_count == 1;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				#(scheme.pdcm_period * 1us);
				
				`spi_frame_begin
					`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b01 << channel;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
			end
		end
		#1ms;
		
		`spi_frame_begin
			`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; pdcm_buffer == 1'b1;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
	endtask
endclass