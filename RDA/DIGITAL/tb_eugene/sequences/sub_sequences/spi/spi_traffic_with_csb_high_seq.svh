class spi_traffic_with_csb_high_seq extends base_dsi_master_seq;

	`uvm_object_utils(spi_traffic_with_csb_high_seq)
	
	function new(string name = "");
		super.new("spi_traffic_with_csb_high");
	endfunction : new
	
	virtual task run_tests();
		log_sim_description("SPI bit errors (too few CRC bits))", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		m_spi_agent.m_config.csb_handler = always_high_csb_hander::create(); 

		`spi_frame_begin
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1; )
		`spi_frame_end
		#100us;	
		`spi_frame_begin
			`spi_frame_create(spi_read_status_seq,)
		`spi_frame_end
		#300us;
		transaction_recorder.expect_tr_count_for_all_channels(0);
				
		// restore default CSB handling
		m_spi_agent.m_config.csb_handler = per_word_csb_hander::create();
		
		`spi_frame_begin
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1; )
		`spi_frame_end
		#500us;
		`spi_frame_begin
			`spi_frame_create(spi_read_crm_data_packets_seq, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		transaction_recorder.disable_recorder();
	endtask
endclass
