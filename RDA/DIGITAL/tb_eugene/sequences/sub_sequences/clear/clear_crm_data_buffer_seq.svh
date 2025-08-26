class clear_crm_data_buffer_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(clear_crm_data_buffer_seq) 
	
	function new(string name = "");
		super.new("clear_crm_data_buffer");
	endfunction
	
	virtual task run_tests();

		log_sim_description("clear data of CRM after CRM on all channels is finished", LOG_LEVEL_SEQUENCE);
		
		`spi_frame_begin
			`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; crm_buffer == 1'b1; pdcm_buffer == 1'b1;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			for (int crm_flag = 0; crm_flag < 2; crm_flag++) begin
				spi_read_crm_data_packets_seq read_seq;
	
				log_sim_description($sformatf("clear CRM data buffer on channel %1d, crm_buffer = %1b", channel, crm_flag), LOG_LEVEL_OTHERS);
	
				`spi_frame_begin
					`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				wait_for_dab();
				#50us;
				
				// don't clear CRM buffer if crm_buffer flag is not set!
				`spi_frame_begin
					`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'(1<<channel); crm_buffer == crm_flag[0];)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				#50us;
				
				`spi_frame_begin
					`spi_frame_send(read_seq, channel_bits == 2'b11;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				
				for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
					if(crm_flag == 0) begin
						read_seq.expect_symbol_count(i, 8'd8);
					end
					else begin
						read_seq.expect_symbol_count(i, (i == channel) ? 'd0 : 8'd8);
					end
				end
				#100us;
			end
		end
		#100us;
	endtask
endclass