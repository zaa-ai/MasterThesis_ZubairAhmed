class clear_queue_during_sync_seq extends dsi3_sync_base_seq;
	
	`uvm_object_utils(clear_queue_during_sync_seq) 
	
	function new(string name = "");
		super.new("clear_queue_during_sync");
	endfunction
	
	virtual task run_tests();
		log_sim_description("clear DSI command queue during synchronize CRM", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		registers.write_and_check_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.SYNC_PDCM, 0);
		registers.write_and_check_register(regmodel.DSI_common.common_DSI3_block_registers.DSI_TX_SHIFT, 0);
		
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			log_sim_description($sformatf("clear command queue of DSI channel %0d during sync CRM", channel), LOG_LEVEL_OTHERS);
			transaction_recorder.clear_all();
			clear_all_SYNC_ERR();
			
			`spi_frame_begin
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
				`spi_frame_create(spi_sync_dsi_channels_seq, external_sync == 1'b0; channel_bits == 2'b11;)
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#350us;
			`spi_frame_begin
				`spi_frame_create(spi_clear_dsi_command_queue_seq, channel_bits == 2'b01 << channel;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
					
			#1ms;
			for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
				check_SYNC_ERR(i, (channel == i) ? 1'b1 : 1'b0);
				clear_SYNC_ERR(i);
			end
			
			expect_dsi_stat_sync_flag(~(2'b01 << channel));
			for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
				// expect one master transmissions for all channels (one channel has been cleared, the others are waiting for sync)
				transaction_recorder.expect_tr_count(i, 1 );
			end
			
			// clear queue for all for next iteration
			`spi_frame_begin
				`spi_frame_create(spi_clear_dsi_command_queue_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			// there must be no more SYNC_ERR at the end 
			for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
			check_SYNC_ERR(i, (channel != i) ? 1'b1 : 1'b0);
		end
		#100us;
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