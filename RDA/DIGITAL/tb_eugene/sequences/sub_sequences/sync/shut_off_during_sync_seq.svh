class shut_off_during_sync_seq extends dsi3_sync_base_seq;
	
	`uvm_object_utils(shut_off_during_sync_seq) 
	
	function new(string name = "");
		super.new("shut_off_during_sync");
	endfunction
	
	virtual task run_tests();
		log_sim_description("disable DSI channel during synchronize CRM", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		// disable checker because it's not able to handle shut-off conditions		
		get_checker_config().disable_all_master_transmission_checkers();
		
		registers.write_and_check_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.SYNC_PDCM, 0);
		registers.write_and_check_register(regmodel.DSI_common.common_DSI3_block_registers.DSI_TX_SHIFT, 0);
			
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			logic[project_pkg::DSI_CHANNELS-1:0] channel_mask;
					
			log_sim_description($sformatf("disable DSI channel %0d during sync CRM", channel), LOG_LEVEL_OTHERS);
			clear_all_SYNC_ERR();
			
			`spi_frame_begin
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
				`spi_frame_create(spi_sync_dsi_channels_seq, external_sync == 1'b0; channel_bits == 2'b11;)
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#350us;
			for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
				if(transaction_recorder.get_master_tr_count(i) != 1) `uvm_error(this.get_name(), $sformatf("Expected a master transaction at channel %0d, but there seems to be none.", i)) 
			end
			channel_mask = 2'b11 & ~(2'b01 << channel);
			// disable this channel
			regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status, channel_mask);
			#1ms;
			for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
				check_SYNC_ERR(i, (channel == i) ? 1'b1 : 1'b0);
				clear_SYNC_ERR(i);
			end
			expect_dsi_stat_sync_flag(channel_mask);
			
			regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status, 2'b11);
			
			// there must be no more SYNC_ERR at the end 
			for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
				check_SYNC_ERR(i, 1'b0);
            end
            
    		// switch off and on to clear all queues
    		regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status, 2'b00);
    		regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status, 2'b11);
            
            // clear_all_interrupts
			for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
                regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.write(status, 16'hffff); // clear all DSI interrupts
            end
            
			#100us;
    		transaction_recorder.clear_all();
		end
		
		`spi_frame_begin
			`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; crm_buffer == 1'b1; pdcm_buffer == 1'b0;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end	
		
		get_checker_config().enable_all_master_transmission_checkers();
		
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
		transaction_recorder.disable_recorder();

	endtask
endclass