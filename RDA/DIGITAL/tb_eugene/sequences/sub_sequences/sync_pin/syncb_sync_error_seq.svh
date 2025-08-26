class syncb_sync_error_seq extends dsi3_sync_base_seq;
	
	`uvm_object_utils(syncb_sync_error_seq) 
	
	function new(string name = "");
		super.new("syncb_sync_error");
	endfunction
	
	virtual task run_tests();
		log_sim_description("sync error at waiting for SYCB pin", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		set_syncb(1'b0);
		#100us;
		transaction_recorder.clear_all();
		`spi_frame_begin
			`spi_frame_create(spi_sync_dsi_channels_seq, external_sync == 1'b1; channel_bits == 2'b11;)
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#300us;
		`spi_frame_begin
			`spi_frame_create(spi_clear_dsi_command_queue_seq, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#300us;
		for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
			transaction_recorder.expect_tr_count(i, 0);
			check_SYNC_ERR(i, 1'b1);
			clear_SYNC_ERR(i);
		end
		set_syncb(1'b1);
		#500us;
		for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
			transaction_recorder.expect_tr_count(i, 0);
			check_SYNC_ERR(i, 1'b0);
		end
		transaction_recorder.disable_recorder();
	endtask	
endclass