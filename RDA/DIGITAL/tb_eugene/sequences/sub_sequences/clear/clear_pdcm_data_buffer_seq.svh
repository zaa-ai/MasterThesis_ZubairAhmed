class clear_pdcm_data_buffer_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(clear_pdcm_data_buffer_seq) 
	
	function new(string name = "");
		super.new("clear_pdcm_data_buffer");
	endfunction
	
	virtual task run_tests();
		tdma_scheme_pdcm scheme = new();

		log_sim_description("clear data of PDCM after PDCM on all channels is finished", LOG_LEVEL_SEQUENCE);
		
		if(!scheme.randomize() with {packets.size() == 1; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)
		set_tdma_scheme_pdcm(0, scheme);
		set_tdma_scheme_pdcm(1, scheme);
		
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			for (int pdcm_flag = 0; pdcm_flag < 2; pdcm_flag++) begin
				spi_read_pdcm_frame_seq read_seq;
	
				log_sim_description($sformatf("clear PDCM data buffer on channel %1d, pdcm_buffer = %1b", channel, pdcm_flag), LOG_LEVEL_OTHERS);
	
				`spi_frame_begin
					`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 1;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				#(scheme.pdcm_period * 1us + 100us);
				
				// don't clear PDCM buffer if pdcm_buffer flag is not set!
				`spi_frame_begin
					`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'(1<<channel); pdcm_buffer == pdcm_flag[0];)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				#50us;
				
				`spi_frame_begin
					`spi_frame_send(read_seq, channel_bits == 2'b11;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				
				for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
					if(pdcm_flag == 0) begin
						read_seq.expect_symbol_count(i, 0, scheme.packets[0].symbol_count);
					end
					else begin
						read_seq.expect_symbol_count(i, 0, (i == channel) ? 0 : scheme.packets[0].symbol_count);
					end
				end
				#100us;
			end
		end
		#100us;
	endtask
endclass