class clear_queue_of_all_channels_during_sync_seq extends dsi3_sync_base_seq;
	
	`uvm_object_utils(clear_queue_of_all_channels_during_sync_seq) 
	
	function new(string name = "");
		super.new("clear_queue_of_all_channels_during_sync");
	endfunction
	
	virtual task run_tests();
		log_sim_description("clear DSI command queue of all channels during synchronize CRM", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		clear_all_SYNC_ERR();
		
		`spi_frame_begin
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
			`spi_frame_create(spi_sync_dsi_channels_seq, external_sync == 1'b0; channel_bits == 2'b11;)
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#350us;
		`spi_frame_begin
			`spi_frame_create(spi_clear_dsi_command_queue_seq, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
				
		#1ms;
		for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
			check_SYNC_ERR(i, 1'b1);
			clear_SYNC_ERR(i);
		end
		
		for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
			// expect one master transmissions for all channels (one channel has been cleared, the others are waiting for sync)
			transaction_recorder.expect_tr_count(i, 1 );
		end
		
		// after all: do a CRM on all channels to see if transmission works correctly
		transaction_recorder.clear_all();
		`spi_frame_begin
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#400us;
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			if(transaction_recorder.get_master_tr_count(channel) == 0) `uvm_error(this.get_name(), $sformatf("Expected a master transaction at channel %0d, but there seems to be none.", channel)) 
		end
		
		transaction_recorder.disable_recorder();
	endtask
endclass