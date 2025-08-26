class crm_maximum_CRM_TIME_with_multiple_answers_seq extends base_dsi_master_seq;

	`uvm_object_utils(crm_maximum_CRM_TIME_with_multiple_answers_seq)
	
	function new(string name = "");
		super.new("crm_maximum_CRM_TIME_with_multiple_answers");
	endfunction
	
	virtual task run_tests();
		int crm_time = 900;
		log_sim_description($sformatf("CRM with maximum CRM_TIME and multiple slave responses"), LOG_LEVEL_SEQUENCE);
		
		registers.write_and_check_register(regmodel.DSI_common.common_DSI3_block_registers.CRM_TIME, 16'(crm_time));
					
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			tdma_scheme scheme;
			dsi3_crm_packet next_packet_1 = random_crm_packet();
			dsi3_crm_packet next_packet_2 = random_crm_packet();
			dsi3_crm_packet next_packet_3 = random_crm_packet();
			
			scheme = tdma_scheme_crm::valid_with_data(next_packet_1.get_word(0), next_packet_1.get_word(1));
			tdma_scheme_crm::add_crm_packet(scheme, next_packet_2.get_word(0), next_packet_2.get_word(1));
			tdma_scheme_crm::add_crm_packet(scheme, next_packet_3.get_word(0), next_packet_3.get_word(1));
			
			scheme.packets[0].set_start_time_window(300, 300);
			scheme.packets[1].set_start_time_window(500, 500);
			scheme.packets[2].set_start_time_window(700, 700);
			
			add_slave_crm_scheme(channel, scheme);
		end
		
		`spi_frame_begin
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 0;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		fork
			begin
				#450us;
				`spi_frame_begin
					`spi_frame_create(spi_read_crm_data_packets_seq, channel_bits == 2'b11;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)	
				`spi_frame_end
			end
			begin
				#650us;
				`spi_frame_begin
					`spi_frame_create(spi_read_crm_data_packets_seq, channel_bits == 2'b11;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)	
				`spi_frame_end
			end
			begin
				#850us;
				`spi_frame_begin
					`spi_frame_create(spi_read_crm_data_packets_seq, channel_bits == 2'b11;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)	
				`spi_frame_end
			end
		join

		// restore some defaults
		registers.reset_register(regmodel.DSI_common.common_DSI3_block_registers.CRM_TIME);
	endtask
	
	virtual function dsi3_crm_packet random_crm_packet();
		dsi3_crm_packet packet = new();
		if(!packet.randomize()) `uvm_error(this.get_name(), "randomization error")
		return packet;
	endfunction
endclass