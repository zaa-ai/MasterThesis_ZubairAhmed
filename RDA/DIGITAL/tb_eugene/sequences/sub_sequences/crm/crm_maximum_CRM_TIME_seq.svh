class crm_maximum_CRM_TIME_seq extends base_dsi_master_seq;

	`uvm_object_utils(crm_maximum_CRM_TIME_seq)
	
	function new(string name = "");
		super.new("crm_maximum_CRM_TIME");
	endfunction
	
	virtual task run_tests();
		int crm_time = 'h7FF;
		log_sim_description($sformatf("CRM with maximum CRM_TIME setting"), LOG_LEVEL_SEQUENCE);
		
		for (dsi3_pkg::dsi3_bit_time_e bit_time=dsi3_pkg::BITTIME_8US; bit_time < dsi3_pkg::BITTIME_UNUSED; bit_time = bit_time.next()) begin
			registers.write_and_check_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.BITTIME, bit_time);
			registers.write_and_check_register(regmodel.DSI_common.common_DSI3_block_registers.CRM_TIME, 16'(crm_time));
					
			log_sim_description($sformatf("CRM with a bit time of %s and CRM_TIME = %0d", bit_time.name(), crm_time), LOG_LEVEL_OTHERS);
			
			for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
				tdma_scheme scheme;
				dsi3_crm_packet next_packet = new();
				if(!next_packet.randomize()) `uvm_error(this.get_name(), "randomization error")
				scheme = tdma_scheme_crm::valid_with_data(next_packet.get_word(0), next_packet.get_word(1), 3, bit_time);
				scheme.packets[0].earliest_start_time = crm_time - 24*1.05*3 - 20;
				scheme.packets[0].latest_start_time = scheme.packets[0].earliest_start_time;
				add_slave_crm_scheme(channel, scheme);
			end
			
			`spi_frame_begin
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			#(crm_time * 1us);
			#100us;
			
			`spi_frame_begin
				`spi_frame_create(spi_read_crm_data_packets_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)	
			`spi_frame_end
			#100us;
		end

		// restore some defaults
		registers.reset_register(regmodel.DSI_common.common_DSI3_block_registers.CRM_TIME);
		registers.reset_register(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG);
	endtask
endclass