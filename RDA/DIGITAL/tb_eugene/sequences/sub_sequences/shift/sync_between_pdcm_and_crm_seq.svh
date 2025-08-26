class sync_between_pdcm_and_crm_seq extends dsi3_sync_base_seq;
	
	`uvm_object_utils(sync_between_pdcm_and_crm_seq) 
	
	function new(string name = "");
		super.new("sync_between_pdcm_and_crm");
	endfunction

	virtual task run_tests();
		tdma_scheme_pdcm_denso scheme = new();
		log_sim_description("synchronization of start between PDCM and CRM", LOG_LEVEL_SEQUENCE);
		apply_tdma_scheme(scheme);
		
		regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.SYNC_PDCM.write(status, 1'b1);
		regmodel.DSI_common.common_DSI3_block_registers.DSI_TX_SHIFT.SHIFT.write(status, 10);
		
		transaction_recorder.enable_recorder();
		transaction_recorder.clear_all();

		`spi_frame_begin
			`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b01; pulse_count == 5;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#900us;
		`spi_frame_begin
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b10; broad_cast == 1'b0;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end

		#5ms;
		
		expect_tx_shift(2'b01, 5, 10);
		expect_tx_shift(2'b10, 1, 10);
		
		transaction_recorder.disable_recorder();
	endtask
endclass