class shut_off_before_sync_seq extends dsi3_sync_base_seq;
	
	`uvm_object_utils(shut_off_before_sync_seq) 
	
	function new(string name = "");
		super.new("shut_off_before_sync");
	endfunction
	
	virtual task run_tests();
		log_sim_description("disable DSI channel before synchronizing CRM", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
			
		for (int channels=1; channels < 2**project_pkg::DSI_CHANNELS; channels++) begin
					
			log_sim_description($sformatf("disable DSI channels 0b%0b before sync CRM", channels), LOG_LEVEL_OTHERS);
			transaction_recorder.clear_all();
			clear_all_SYNC_ERR();
			
			// disable channel(s)
			regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status, 2'(~channels));
			#50us;
			
			`spi_frame_begin
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
				`spi_frame_create(spi_sync_dsi_channels_seq, external_sync == 1'b0; channel_bits == 2'b11;)
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#1ms;
					
			for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
				transaction_recorder.expect_tr_count(i, (channels[i] == 1'b1) ? 0 : 1);
				// check and clear SYNC_ERR for disabled channel
				check_SYNC_ERR(i, (channels[i] == 1'b1) ? 1'b1 : 1'b0);
				clear_SYNC_ERR(i);
				// check and clear COM_ERR for disabled channel
				registers.check_flag(regmodel.DSI[i].DSI3_channel_registers.DSI_IRQ_STAT.COM_ERR, (channels[i] == 1'b1) ? 1'b1 : 1'b0);
				regmodel.DSI[i].DSI3_channel_registers.DSI_IRQ_STAT.COM_ERR.write(status, 1'b1);
				// check DSI_STAT.SYNC				
				registers.check_flag(regmodel.DSI[i].DSI3_channel_registers.DSI_STAT.SYNC, (channels[i] == 1'b1) ? 1'b0 : 1'b1);
			end
			#100us;
			
			`spi_frame_begin
				`spi_frame_create(spi_clear_dsi_command_queue_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status, 2'b11);
			#100us;
		end
		
		// after all: do a CRM on all channels to see if transmission works correctly
		transaction_recorder.clear_all();
		`spi_frame_begin
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#450us;
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			if(transaction_recorder.get_master_tr_count(channel) == 0) `uvm_error(this.get_name(), $sformatf("Expected a master transaction at channel %0d, but there seems to be none.", channel)) 
		end
		
		clear_all_SYNC_ERR();
		transaction_recorder.disable_recorder();
	endtask
endclass