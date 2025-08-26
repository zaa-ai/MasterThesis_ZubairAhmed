class crm_CRM_TIME_lower_than_transmission_time_seq extends base_dsi_master_seq;

	`uvm_object_utils(crm_CRM_TIME_lower_than_transmission_time_seq)
	
	function new(string name = "");
		super.new("crm_CRM_TIME_lower_than_transmission_time");
	endfunction
	
	virtual task run_tests();
		log_sim_description($sformatf("CRM with a minimum CRM_TIME setting"), LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		for (dsi3_pkg::dsi3_bit_time_e bit_time=dsi3_pkg::BITTIME_8US; bit_time < dsi3_pkg::BITTIME_UNUSED; bit_time = bit_time.next()) begin
			int crm_transmission_duration = 256 * dsi3_pkg::get_bit_time_factor(bit_time);
			registers.write_and_check_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.BITTIME, bit_time);
			
			for (int with_response = 0; with_response < 2; with_response++) begin
				for (int crm_time = 0; crm_time < crm_transmission_duration; crm_time += 50) begin
					
					log_sim_description($sformatf("CRM with a bit time of %s and CRM_TIME = %0d %s", bit_time.name(), crm_time, (with_response == 1) ? "with slave response" : "without slave response"), LOG_LEVEL_OTHERS);
					registers.write_and_check_register(regmodel.DSI_common.common_DSI3_block_registers.CRM_TIME, crm_time);
					
					for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
						if(with_response == 1) begin
							dsi3_crm_packet next_packet = new();
							if(!next_packet.randomize()) `uvm_error(this.get_name(), "randomization error")
							add_slave_crm_scheme(channel, tdma_scheme_crm::valid_with_data(next_packet.get_word(0), next_packet.get_word(1), 3, bit_time));
						end
						else begin
							add_slave_crm_scheme(channel, tdma_scheme_crm::no_answer());
						end
					end
					
					check_dab(1'b1);
					
					`spi_frame_begin
						`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 0;)
						`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
					`spi_frame_end
					
					#((crm_transmission_duration+50) * 1us);
					check_dab(1'b0);
					#((24*1.05*3 + 50) * 1us);
					
					`spi_frame_begin
						`spi_frame_create(spi_read_crm_data_packets_seq, channel_bits == 2'b11;)
						`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)	
					`spi_frame_end
					#100us;
				end
			end
		end

		// restore some defaults
		registers.reset_register(regmodel.DSI_common.common_DSI3_block_registers.CRM_TIME);
		registers.reset_register(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG);
		transaction_recorder.disable_recorder();
	endtask
endclass