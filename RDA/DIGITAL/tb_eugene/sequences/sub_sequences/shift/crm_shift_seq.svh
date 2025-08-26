class crm_shift_seq extends dsi3_sync_base_seq;
	
	`uvm_object_utils(crm_shift_seq) 
	
	function new(string name = "");
		super.new("crm_shift");
	endfunction

	virtual task run_tests();
		log_sim_description("check shifting in CRM", LOG_LEVEL_SEQUENCE);
		regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.CRC_EN.write(status, 1'b0);
		transaction_recorder.enable_recorder();
		
		`spi_frame_begin
			`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; crm_buffer == 1'b1;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		for (dsi3_pkg::dsi3_bit_time_e bit_time = dsi3_pkg::BITTIME_8US; bit_time < dsi3_pkg::BITTIME_UNUSED; bit_time = bit_time.next()) begin
			int crm_duration;
			crm_duration = int'(320*dsi3_pkg::get_bit_time_factor(bit_time) + 24*1.05*3 + 30);
			registers.write_and_check_register(regmodel.DSI_common.common_DSI3_block_registers.CRM_TIME, crm_duration);
			
			regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.BITTIME.write(status, bit_time);
			set_tdma_scheme_crm(0, tdma_scheme_crm::valid(3, bit_time));
			set_tdma_scheme_crm(1, tdma_scheme_crm::valid(3, bit_time));
			
			for(int shift = 0; shift <= get_max_shift(); shift++) begin
				registers.write_and_check_register(regmodel.DSI_common.common_DSI3_block_registers.DSI_TX_SHIFT, shift);

				log_sim_description($sformatf("check shifting in CRM at bit_time=%s with shift=%3d and CRM_TIME=%0d", bit_time.name(), shift, crm_duration), LOG_LEVEL_OTHERS);
				transaction_recorder.clear_all();
				
				`spi_frame_begin
					`spi_frame_create(spi_sync_dsi_channels_seq, external_sync == 1'b0; channel_bits == 2'b11;)
					`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				#(crm_duration*1us + 50us);
				
				expect_tx_shift(2'b11, 1, shift, 25ns);
				`spi_frame_begin
					`spi_frame_create(spi_read_crm_data_packets_seq, channel_bits == 2'b11;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				#100us;
			end
		end
		
		set_tdma_scheme_crm(0, tdma_scheme_crm::valid());
		set_tdma_scheme_crm(1, tdma_scheme_crm::valid());
		registers.reset_register(regmodel.DSI_common.common_DSI3_block_registers.DSI_TX_SHIFT);
		registers.reset_register(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG);
		transaction_recorder.disable_recorder();
	endtask
endclass