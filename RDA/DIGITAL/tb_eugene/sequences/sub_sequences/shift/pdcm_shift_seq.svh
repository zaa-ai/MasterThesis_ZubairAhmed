class pdcm_shift_seq extends dsi3_sync_base_seq;
	
	rand bit sync_pdcm;
	
	`uvm_object_utils(pdcm_shift_seq) 
	
	function new(string name = "");
		super.new("pdcm_shift");
	endfunction

	virtual task run_tests();
		int period_count = 3;
		log_sim_description($sformatf("check shifting in PDCM with sync_pdcm=%1b", sync_pdcm), LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		`spi_frame_begin
			`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; pdcm_buffer == 1'b1;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.SYNC_PDCM.write(status, sync_pdcm);
		
		for (dsi3_pkg::dsi3_bit_time_e bit_time = dsi3_pkg::BITTIME_8US; bit_time < dsi3_pkg::BITTIME_UNUSED; bit_time = bit_time.next()) begin
			tdma_scheme_pdcm scheme = new();
			regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.BITTIME.write(status, bit_time);

			if(!scheme.randomize() with {packets.size() inside {[1:6]}; symbol_count_min == 4; symbol_count_max == 16; chiptime == 3; bit_time == local::bit_time;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
			apply_tdma_scheme(scheme);
			
			for(int shift = 0; shift <= get_max_shift(); shift++) begin
				
				log_sim_description($sformatf("check shifting in PDCM (sync_pdcm=%1b and bit_time=%s) with shift=%3d", sync_pdcm, bit_time.name(), shift), LOG_LEVEL_OTHERS);
				registers.write_and_check_register(regmodel.DSI_common.common_DSI3_block_registers.DSI_TX_SHIFT, shift);
				
				`spi_frame_begin
					`spi_frame_create(spi_sync_dsi_channels_seq, channel_bits == 2'b11; external_sync == 1'b0;)
					`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 8'(period_count);)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				#((period_count*scheme.pdcm_period)*1us + 100us);
				
				expect_tx_shift(2'b11, 3, shift, 25ns);
				transaction_recorder.clear_all();
		
				// check results
				for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
					for(int period_index=0; period_index < period_count; period_index++) begin
						`spi_frame_begin
							`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b01 << channel;)
							`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
						`spi_frame_end
					end
				end
			end
		end
		
		registers.reset_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.BITTIME);
		registers.reset_register(regmodel.DSI_common.common_DSI3_block_registers.DSI_TX_SHIFT);
	endtask
endclass