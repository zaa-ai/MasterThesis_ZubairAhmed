class pdcm_shift_sync_change_during_pdcm_seq extends dsi3_sync_base_seq;
	
	`uvm_object_utils(pdcm_shift_sync_change_during_pdcm_seq) 
	
	function new(string name = "");
		super.new("pdcm_shift_sync_change_during_pdcm");
	endfunction

	virtual task run_tests();
		int period_count = 3;
		tdma_scheme_pdcm scheme = new();
		log_sim_description($sformatf("change PDCM sync for different channels"), LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		if(!scheme.randomize() with {packets.size() == 1; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		apply_tdma_scheme(scheme);
		
		repeat(10) begin	
			transaction_recorder.clear_all();
			regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.SYNC_PDCM.write(status, 1'b1);
						
			`spi_frame_begin
				`spi_frame_create(spi_pdcm_seq, 	channel_bits == 2'b01; pulse_count == 8'(period_count);)
				`spi_frame_create(spi_dsi_wait_seq, channel_bits == 2'b10; wait_time inside {[15'd50:15'd120]};)
				`spi_frame_create(spi_pdcm_seq, 	channel_bits == 2'b10; pulse_count == 8'(period_count);)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			fork
				begin
					int delay = $urandom_range(100, 600); 
					#(delay * 1us);
					// change PDCM SYNC
					regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.SYNC_PDCM.write(status, 1'b0);
				end
				begin
					#(((period_count+1) * scheme.pdcm_period)*1us);
				end
			join
				
			// check results
			for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
				transaction_recorder.expect_tr_count(channel, period_count);
				for(int period_index=0; period_index < period_count; period_index++) begin
					`spi_frame_begin
						`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b01 << channel;)
						`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
					`spi_frame_end
				end
			end
		end
		
		regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.SYNC_PDCM.write(status, 1'b1);
		transaction_recorder.disable_recorder();
	endtask
endclass