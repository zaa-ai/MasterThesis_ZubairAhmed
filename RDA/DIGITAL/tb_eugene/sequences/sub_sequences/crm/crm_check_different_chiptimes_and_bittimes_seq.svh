class crm_check_different_chiptimes_and_bittimes_seq extends base_dsi_master_seq;

	`uvm_object_utils(crm_check_different_chiptimes_and_bittimes_seq)
	
	function new(string name = "");
		super.new("crm_check_different_chiptimes_and_bittimes");
	endfunction : new
	
	virtual task run_tests();
		dsi3_pkg::dsi3_bit_time_e bit_time;
		chip_times_iterator_with_register_model chip_iterator = new(regmodel);
		
		log_sim_description($sformatf("do CRM with different chip times and different TX bit times"), LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		// disable CRC check
		registers.write_and_check_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.CRC_EN, 1'b0);
		
		for (bit_time=dsi3_pkg::BITTIME_8US; bit_time < dsi3_pkg::BITTIME_UNUSED; bit_time = bit_time.next()) begin
			registers.write_and_check_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.BITTIME, bit_time);

			chip_iterator.restart();
			while(chip_iterator.has_next()) begin
				int chip_time = chip_iterator.get_current();
				int crm_duration;
				dsi3_crm_packet packets[$];
				spi_read_crm_data_packets_seq read_seq;
				spi_crm_seq crm_seq;
				
				log_sim_description($sformatf("do CRM with chip time of %2dus and TX bit time %s", chip_time, bit_time.name()), LOG_LEVEL_OTHERS);
				transaction_recorder.clear_all();

				chip_iterator.apply_next();
				check_DSI_CMD(CMD_STATUS_READ);
				`ifndef GATE_LEVEL
				check_value_at_path(`STRING_OF(`DSI_RX_FILTER_FAST), chip_time == 2 ? 'b11 : 0);
				`endif
				
				// define response data
				for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
					dsi3_crm_packet next_packet = new();
					if(!next_packet.randomize()) `uvm_error(this.get_name(), "randomization error")
					packets.push_back(next_packet);
					add_slave_crm_scheme(channel, tdma_scheme_crm::valid_with_data(next_packet.get_word(0), next_packet.get_word(1), chip_time, bit_time));
				end
				
				crm_duration = int'(320*dsi3_pkg::get_bit_time_factor(bit_time) + 24*1.05*chip_time + 30);
				registers.write_and_check_register(regmodel.DSI_common.common_DSI3_block_registers.CRM_TIME, crm_duration);
				`uvm_info(this.get_name(), $sformatf("wrote CRM_TIME register to value %0d", crm_duration), UVM_MEDIUM)

				`spi_frame_begin
					`spi_frame_send(crm_seq, channel_bits == 2'b11; broad_cast == 0;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				
				#20us;
				fork
					#(crm_duration * 1us);
					begin
						check_dab(1'b1);
						check_DSI_CMD(CMD_CRM);
					end
				join
				check_dab(1'b0);
				check_DSI_CMD(CMD_STATUS_READ);
				
				`spi_frame_begin
					`spi_frame_send(read_seq, channel_bits == 2'b11;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)	
				`spi_frame_end
		
				// check results
				for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
					transaction_recorder.expect_packets(channel, {crm_seq.crm_packet});
				
					read_seq.expect_flags(2'(channel), {}); // there must be no CRC flag since CRC_EN = 0
					read_seq.expect_symbol_count(2'(channel), 8'd8);
					read_seq.expect_packet_data(2'(channel), 0, packets[channel].get_word(0));
					read_seq.expect_packet_data(2'(channel), 1, packets[channel].get_word(1));
					
					check_DSI_CMD_HIGH_LOW(channel, crm_seq.crm_packet);
					check_PKG_STAT(channel, 1'b0);
				end
				
				check_dab(1'b1);
				#1ms;
			end
		end
			
		// restore some defaults
		registers.reset_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.CRC_EN);
		registers.reset_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.BITTIME);
		registers.reset_register(regmodel.DSI_common.common_DSI3_block_registers.CRM_TIME);
		chip_iterator.apply_default();
		transaction_recorder.disable_recorder();
		transaction_recorder.clear_all();
	endtask
endclass