class clear_single_channel_buffer_during_pdcm_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(clear_single_channel_buffer_during_pdcm_seq) 
	
	function new(string name = "");
		super.new("clear_single_channel_buffer_during_pdcm");
	endfunction
	
	virtual task run_tests();
		tdma_scheme_pdcm scheme = new();
		
		log_sim_description("clear single buffers during PDCM reception", LOG_LEVEL_SEQUENCE);
		
		if(!scheme.randomize() with {packets.size() == 1; symbol_count_min == 32; symbol_count_max == 32; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)
		set_tdma_scheme_pdcm(0, scheme);
		set_tdma_scheme_pdcm(1, scheme);
		
		for(int clear_channel=0; clear_channel < 2 ** project_pkg::DSI_CHANNELS; clear_channel++) begin
			spi_read_pdcm_frame_seq read_1, read_2;
			
			log_sim_description($sformatf("clear PDCM data on channels 0b%2b during PDCM reception", clear_channel), LOG_LEVEL_OTHERS);
	
			`spi_frame_begin
				`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; pdcm_buffer == 1'b1;)
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 8'd1;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#(scheme.pdcm_period * 1us + 100us);
			
			`spi_frame_begin
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 8'd1;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#(scheme.pdcm_period/2 * 1us);
			`spi_frame_begin
			`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'(clear_channel); pdcm_buffer == 1'b1;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			#(scheme.pdcm_period * 1us);
			`spi_frame_begin
				`spi_frame_send(read_1, channel_bits == 2'b11;)
				`spi_frame_send(read_2, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			// check results
			for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
				read_1.expect_symbol_count(2'(channel), 0, 8'd32);
				read_2.expect_symbol_count(2'(channel), 0, (clear_channel[channel] == 1'b1) ? 8'd0 : 8'd32);
			end
		end
		#100us;
	endtask
	
endclass