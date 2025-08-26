class crm_crc_en_seq extends base_dsi_master_seq;

	`uvm_object_utils(crm_crc_en_seq)
	
	function new(string name = "");
		super.new("crm_crc_en");
	endfunction : new
	
	virtual task run_tests();
		spi_read_crm_data_packets_seq read;
		spi_crm_seq crm_seq;
		
		log_sim_description("CRM transmit with different CRC_EN, broad cast and wrong/correct CRC", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		for(int crc_en=0; crc_en <= 1; crc_en++) begin
			registers.write_and_check_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.CRC_EN, crc_en);
			for(int bc=0; bc<=1; bc++) begin
				for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
					for(int crc_correct=0; crc_correct<=1; crc_correct++) begin
						tdma_scheme scheme;
						dsi3_crm_packet packet = new();
						if(!packet.randomize()) `uvm_error(this.get_name(), "randomization error")	
						
						log_sim_description($sformatf("CRM transmit CRC_EN=%0b, BROAD_CAST=%1b, CRC correct = %0b at channel %0d", crc_en, bc, crc_correct, channel), LOG_LEVEL_OTHERS);
						transaction_recorder.clear_all();
						
						scheme = tdma_scheme_crm::valid_with_data(packet.get_word(0), packet.get_word(1));
						if(bc) scheme.packets[0].enable = 1'b0;
						add_slave_crm_scheme(channel, scheme);
						
						`spi_frame_begin
							`spi_frame_send(crm_seq, channel_bits == 2'b01 << channel; broad_cast == 1'(bc); dsi3_crc_correct == 1'(crc_correct);)
							`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
						`spi_frame_end
						#500us;
						`spi_frame_begin
							`spi_frame_send(read, channel_bits == 2'b01 << channel;)
							`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
						`spi_frame_end
						
						if(crc_en) begin
							// calculate a correct CRC for comparison
							crm_seq.crm_packet.crc_correct = 1'b1;
							crm_seq.crm_packet.update_crc();
						end
						
						// check results
						transaction_recorder.expect_packets(channel, {crm_seq.crm_packet});
						check_DSI_CMD_HIGH_LOW(channel, crm_seq.crm_packet);
						
						if(bc) begin
							// broadcast -> expect no data
							read.expect_empty(2'(channel));
						end 
						else begin
							read.expect_flags(2'(channel), (packet.crc_correct || crc_en == 0 ) ? {} : {CRC});
							read.expect_packet(2'(channel), packet, .ignore_crc(1'b1));
							check_PKG_STAT(channel, !packet.crc_correct && crc_en == 1 );
						end
						#100us;
					end
				end
			end
		end
		// restore default
		transaction_recorder.disable_recorder();
		transaction_recorder.clear_all();
		registers.reset_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.CRC_EN);
	endtask
endclass