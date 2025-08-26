class first_sync_at_all_channels_then_single_crms_seq extends dsi3_sync_base_seq;
	
	`uvm_object_utils(first_sync_at_all_channels_then_single_crms_seq) 
	
	function new(string name = "");
		super.new("first_sync_at_all_channels_then_single_crms");
	endfunction
	
	virtual task run_tests();
		time spi_end;
		
		log_sim_description("first synchronize at all channels then CRM transmit on each channel", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		// disable sync PDCM and TX shift
		registers.write_and_check_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.SYNC_PDCM, 0);
		registers.write_and_check_register(regmodel.DSI_common.common_DSI3_block_registers.DSI_TX_SHIFT, 0);
		
		`spi_frame_begin
			`spi_frame_create(spi_sync_dsi_channels_seq, external_sync == 1'b0; channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#50us;
		`spi_frame_begin
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b10; broad_cast == 1'b0;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		expect_dsi_stat_sync_flag(2'b10);
		
		#100us;
		`spi_frame_begin
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b01; broad_cast == 1'b0;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		spi_end = $time;
		#1ms;
		check_channel_sync(2'b11, 2'b11, spi_end);
		
		transaction_recorder.disable_recorder();
	endtask
endclass