class clear_buffer_during_pdcm_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(clear_buffer_during_pdcm_seq) 
	
	function new(string name = "");
		super.new("clear_buffer_during_pdcm");
	endfunction
	
	virtual task run_tests();

		log_sim_description("clear data buffer during PDCM reception", LOG_LEVEL_SEQUENCE);

		for (int delay = 80; delay < 110; delay++) begin
			tdma_scheme_pdcm scheme = new();
			spi_read_pdcm_frame_seq read_1, read_2;
			
			if(!scheme.randomize() with {packets.size() == 1; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
			scheme.packets[0].set_start_time_window(50, 55);
			
			`upload_tdma_scheme_with(scheme, channels == 2'b11;)
			
			scheme.packets[0].set_start_time_window(52, 52);
			set_tdma_scheme_pdcm(0, scheme);
			set_tdma_scheme_pdcm(1, scheme);
			#50us;

			`spi_frame_begin
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 8'd1;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#(scheme.pdcm_period * 1us);
			
			`spi_frame_begin
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 8'd1;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			#(delay * 1us);
			
			`spi_frame_begin
				`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; crm_buffer == 1'b0; pdcm_buffer == 1'b1;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			#((scheme.pdcm_period - delay) * 1us);
			
			`spi_frame_begin
				`spi_frame_send(read_1, channel_bits == 2'b11;)
				`spi_frame_send(read_2, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			read_1.expect_symbol_count(2'd0, 0, scheme.packets[0].symbol_count);
			read_1.expect_symbol_count(2'd1, 0, scheme.packets[0].symbol_count);
			read_2.expect_empty(2'd0, 0);
			read_2.expect_empty(2'd1, 0);
			#100us;
		end
	endtask
endclass