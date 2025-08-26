class crm_read_empty_data_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(crm_read_empty_data_seq)
	
	function new(string name = "");
		super.new("crm_read_empty_data");
	endfunction
	
	task run_tests();
		// clear CRM data from buffer
		`spi_frame_begin
			`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; crm_buffer == 1'b1;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end

		log_sim_description($sformatf("Read empty CRM data on all channels"), LOG_LEVEL_SEQUENCE);
		
		for (int channels=0; channels < 2 ** project_pkg::DSI_CHANNELS; channels++) begin
			`spi_frame_begin
				`spi_frame_create(spi_read_crm_data_packets_seq, channel_bits == 2'(channels);)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#50us;
		end
		
		log_sim_description($sformatf("Read one empty channel and one with data"), LOG_LEVEL_SEQUENCE);
		
		for(int with_answer=0; with_answer < 2; with_answer++) begin
			for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
				
				if(with_answer == 0) begin
					add_slave_crm_scheme(channel, tdma_scheme_crm::no_answer());
				end
				
				`spi_frame_begin
				  `spi_frame_create(spi_crm_seq, channel_bits == 2'b01 << channel; broad_cast == 0;)
				  `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				#500us;
		
				`spi_frame_begin
					`spi_frame_create(spi_read_crm_data_packets_seq, channel_bits == 2'b11;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end	
				#50us;
				// clear CRM data from buffer
				`spi_frame_begin
					`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; crm_buffer == 1'b1;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				#50us;
			end
		end
		#100us;
	endtask
	
endclass