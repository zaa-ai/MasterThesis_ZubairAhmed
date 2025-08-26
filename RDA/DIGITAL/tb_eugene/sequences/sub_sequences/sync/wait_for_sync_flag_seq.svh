class wait_for_sync_flag_seq extends dsi3_sync_base_seq;
	
	`uvm_object_utils(wait_for_sync_flag_seq) 
	
	function new(string name = "");
		super.new("wait_for_sync_flag");
	endfunction
	
	virtual task run_tests();
		log_sim_description("check DSI_STAT.SYNC flag for all channels", LOG_LEVEL_SEQUENCE);
		
		for(int channel=0; channel<project_pkg::DSI_CHANNELS; channel++) begin
			time spi_end;
			log_sim_description($sformatf("check DSI_STAT.SYNC flag for channel %0d", channel), LOG_LEVEL_OTHERS);
			
			transaction_recorder.enable_recorder();
			
			// disable sync PDCM and TX shift
			registers.write_and_check_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.SYNC_PDCM, 0);
			registers.write_and_check_register(regmodel.DSI_common.common_DSI3_block_registers.DSI_TX_SHIFT, 0);
			
			`spi_frame_begin
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
				`spi_frame_create(spi_sync_dsi_channels_seq, external_sync == 1'b0; channel_bits == 2'b11;)
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b01 << channel; broad_cast == 1'b0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#1ms;
			expect_dsi_stat_sync_flag(2'b01 << channel);
			
			`spi_frame_begin
				`spi_frame_create(spi_crm_seq, channel_bits == ~(2'b01 << channel); broad_cast == 1'b0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			spi_end = $time;
			#500us;
			check_channel_sync(2'b11, 2'b11, spi_end);
		end
		transaction_recorder.disable_recorder();
	endtask
endclass