class sync_pdcm_seq extends dsi3_sync_base_seq;
	
	`uvm_object_utils(sync_pdcm_seq) 
	
	function new(string name = "");
		super.new("sync_pdcm");
	endfunction
	
	virtual task run_tests();
		tdma_scheme_pdcm scheme = new();
		
		log_sim_description("synchronize PDCMs", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		if(!scheme.randomize() with {packets.size() inside {[1:5]}; symbol_count_max == 8; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		apply_tdma_scheme(scheme);

		// disable sync PDCM feature
		registers.write_and_check_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.SYNC_PDCM, 0);
		registers.write_and_check_register(regmodel.DSI_common.common_DSI3_block_registers.DSI_TX_SHIFT, 0);
		
		
		for (int sync_channels=0; sync_channels <= 'b11; sync_channels++) begin
			// make sure to always sync at least two channels 
			if($countones(sync_channels) >= 2) begin
				
				for (int channels='b01; channels <= 'b11; channels++) begin
					time spi_end;
					
					log_sim_description($sformatf("sync PDCM with period of %0dus at channels 0b%2b with CRM transmit at channels 0b%2b", scheme.pdcm_period, channels, sync_channels), LOG_LEVEL_OTHERS);
					
					`spi_frame_begin
						`spi_frame_create(spi_pdcm_seq, channel_bits == 2'(channels); pulse_count inside {[1:5]};)
						`spi_frame_create(spi_sync_dsi_channels_seq, external_sync == 1'b0; channel_bits == $size(channel_bits)'(sync_channels);)
						`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 8'd1;)
						`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
					`spi_frame_end
					spi_end = $time;
					#3ms;
					
					check_channel_sync(channels, sync_channels, spi_end);
					transaction_recorder.clear_all();
				end
			end
		end
		transaction_recorder.disable_recorder();
	endtask
endclass