class clear_buffer_and_read_in_one_frame_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(clear_buffer_and_read_in_one_frame_seq) 
	
	function new(string name = "");
		super.new("clear_buffer_and_read_in_one_frame");
	endfunction
	
	virtual task run_tests();
		log_sim_description("clear data buffer and read data in one SPI frame (this is not recommended)", LOG_LEVEL_SEQUENCE);
		
		for(int clear_channel=0; clear_channel < 2 ** project_pkg::DSI_CHANNELS; clear_channel++) begin
			spi_read_crm_data_packets_seq read;
			
			log_sim_description($sformatf("clear CRM data on channels 0b%2b", clear_channel), LOG_LEVEL_OTHERS);
			
			`spi_frame_begin
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#500us;
			
			`spi_frame_begin
				`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'(clear_channel); crm_buffer == 1'b1; pdcm_buffer == 1'b0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1; )
				`spi_frame_send(read, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1; )
			`spi_frame_end
			
			// check results
			for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
				if(clear_channel[channel])begin
					read.expect_empty(2'(channel));
				end 
				else begin
					read.expect_symbol_count(2'(channel), 8'd8);
				end
			end
		end
		#100us;		
	endtask
endclass