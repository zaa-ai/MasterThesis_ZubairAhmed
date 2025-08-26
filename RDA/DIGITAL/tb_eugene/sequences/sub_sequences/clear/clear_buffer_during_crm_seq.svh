class clear_buffer_during_crm_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(clear_buffer_during_crm_seq) 
	
	function new(string name = "");
		super.new("clear_buffer_during_crm");
	endfunction
	
	virtual task run_tests();
		spi_read_crm_data_packets_seq read_1, read_2;
		
		log_sim_description("clear data buffer during CRM reception", LOG_LEVEL_SEQUENCE);
		
		for (int delay = 340; delay < 360; delay++) begin
			// fill some data into buffer
			`spi_frame_begin
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#500us
			
			`spi_frame_begin
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			#(delay * 1us);
			`spi_frame_begin
				`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; crm_buffer == 1'b1; pdcm_buffer == 1'b0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			#((500 - delay) *1us);
			`spi_frame_begin
				`spi_frame_send(read_1, channel_bits == 2'b11;)
				`spi_frame_send(read_2, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			read_2.expect_empty(2'd0);
			read_2.expect_empty(2'd1);
			#100us;
		end
	endtask
endclass