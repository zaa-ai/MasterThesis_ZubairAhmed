class discovery_mode_shift_seq extends dsi3_sync_base_seq;
	
	`uvm_object_utils(discovery_mode_shift_seq) 
	
	function new(string name = "");
		super.new("discovery_mode_shift");
	endfunction

	virtual task run_tests();
		int number_of_slaves = 15;
		
		log_sim_description("check shifting in discovery mode", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		set_tdma_scheme_dm(0, tdma_scheme_dm::valid());
		set_tdma_scheme_dm(1, tdma_scheme_dm::valid());			
		
		`spi_frame_begin
			`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; crm_buffer == 1'b1;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		for (dsi3_pkg::dsi3_bit_time_e bit_time = dsi3_pkg::BITTIME_8US; bit_time < dsi3_pkg::BITTIME_UNUSED; bit_time = bit_time.next()) begin
			edf_parameter_base t__Disc_per__ = get_disc_per(bit_time);
			regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.BITTIME.write(status, bit_time);
			
			for(int shift = 0; shift <= get_max_shift(); shift++) begin
				registers.write_and_check_register(regmodel.DSI_common.common_DSI3_block_registers.DSI_TX_SHIFT, shift);

				log_sim_description($sformatf("check shifting in discovery mode at bit_time=%s with shift=%3d", bit_time.name(), shift), LOG_LEVEL_OTHERS);
				transaction_recorder.clear_all();
				
				`spi_frame_begin
					`spi_frame_create(spi_sync_dsi_channels_seq, external_sync == 1'b0; channel_bits == 2'b11;)
					`spi_frame_create(spi_discovery_mode_seq, channel_bits == 2'b11;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				
				#(t__Disc_per__.get_typ_time() * (number_of_slaves+1));
				#100us;
				expect_tx_shift(2'b11, 16, shift, 25ns);
				#100us;
			end
		end
		
		registers.reset_register(regmodel.DSI_common.common_DSI3_block_registers.DSI_TX_SHIFT);
		registers.reset_register(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG);
		transaction_recorder.disable_recorder();
	endtask
	
	function edf_parameter_base get_disc_per(dsi3_pkg::dsi3_bit_time_e bit_time);
		case (bit_time)
			dsi3_pkg::BITTIME_8US : return edf_parameters.epms.t__Disc_per_8__;
			dsi3_pkg::BITTIME_16US: return edf_parameters.epms.t__Disc_per_16__;
			dsi3_pkg::BITTIME_32US: return edf_parameters.epms.t__Disc_per_32__;
		endcase
		`uvm_error(get_type_name(), $sformatf("failed to get t__Disc_per__ for bit time %s", bit_time))
	endfunction
endclass