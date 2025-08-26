class random_pdcm_and_different_bit_chip_times_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(random_pdcm_and_different_bit_chip_times_seq)

	function new(string name = "");
		super.new("random_pdcm_and_different_bit_chip_times_seq");
	endfunction : new
	
	task run_tests();
		dsi3_pkg::dsi3_bit_time_e bit_time;
		chip_times_iterator_with_register_model chip_iterator = new(regmodel);
		
		log_sim_description($sformatf("PDCM with different chip times and different TX bit times"), LOG_LEVEL_SEQUENCE);
		
		// disable CRC check
		regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.CRC_EN.write(status, 1'b0);
		
		for (bit_time=dsi3_pkg::BITTIME_8US; bit_time < dsi3_pkg::BITTIME_UNUSED; bit_time = bit_time.next()) begin
			regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.BITTIME.write(status, bit_time);

			chip_iterator.restart();
			while(chip_iterator.has_next()) begin
				tdma_scheme_pdcm scheme = new();
				int chip_time = chip_iterator.get_current();
				
				log_sim_description($sformatf("PDCM with chip time of %2dus and TX bit time %s", chip_time, bit_time.name()), LOG_LEVEL_OTHERS);
				
				if(!scheme.randomize() with {packets.size() == 1; chiptime == local::chip_time; bit_time == local::bit_time;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
				`upload_tdma_scheme_with(scheme, channels == 2'b11;)
				set_tdma_scheme_pdcm(0, scheme);
				set_tdma_scheme_pdcm(1, scheme);
				
				chip_iterator.apply_next();
				check_DSI_CMD(CMD_STATUS_READ);
				
				`spi_frame_begin
					`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 3;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				
				#20us;
				fork
					#(3 * scheme.pdcm_period * 1us);
					begin
						check_dab(1'b1);
						check_DSI_CMD(CMD_PDCM);
					end
				join
				check_dab(1'b0);
				check_DSI_CMD(CMD_STATUS_READ);
				
				// read data of all 3 PDCM frames in one SPI frame
				`spi_frame_begin
					`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11;)
					`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11;)
					`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
		
				check_dab(1'b1);
				#1ms;
			end
		end
			
		// restore some default settings
		chip_iterator.apply_default();
		registers.reset_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.BITTIME);
		registers.reset_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.CRC_EN);
	endtask
	
endclass
