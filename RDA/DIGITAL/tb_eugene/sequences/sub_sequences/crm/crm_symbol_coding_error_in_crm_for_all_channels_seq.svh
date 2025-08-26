class crm_symbol_coding_error_in_crm_for_all_channels_seq extends base_dsi_master_seq;

	`uvm_object_utils(crm_symbol_coding_error_in_crm_for_all_channels_seq)
	
	function new(string name = "");
		super.new("crm_symbol_coding_error_in_crm_for_all_channels");
	endfunction : new
	
	virtual task run_tests();
		log_sim_description("receive packets with symbol coding error (SE) on all channels", LOG_LEVEL_SEQUENCE);
		
		for (int error_channel=0; error_channel < project_pkg::DSI_CHANNELS; error_channel++) begin
			spi_read_crm_data_packets_seq read;
			dsi3_crm_packet packets[$];
			
			log_sim_description($sformatf("receive symbol coding error at channel %0d", error_channel), LOG_LEVEL_OTHERS);
			
			get_checker_config().expect_CRM_symbol_coding_error_in_dsi_packet = 'b0;
			get_checker_config().expect_CRM_symbol_coding_error_in_dsi_packet[error_channel] = 1'b1;
			
			for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
				tdma_scheme scheme;
				dsi3_crm_packet next_packet = new();
				if(!next_packet.randomize()) `uvm_error(this.get_name(), "randomization error")
				packets.push_back(next_packet);
				scheme = tdma_scheme_crm::valid_with_data(next_packet.get_word(0), next_packet.get_word(1));
				
				if(channel == error_channel) begin
					// inject SE
					scheme.packets[0].symbol_coding_error_injection = common_env_pkg::ALWAYS_ERROR;
				end
				add_slave_crm_scheme(channel, scheme);
			end
			check_dab(1'b1);
			`spi_frame_begin
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#500us;
			check_dab(1'b0);
			`spi_frame_begin
				`spi_frame_send(read, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq,)
			`spi_frame_end
			check_dab(1'b1);
			// check results
			for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
				dsi_response_flags expected_flags[$] = {};
				if(!packets[channel].crc_correct) expected_flags.push_back(CRC);
				
				read.expect_symbol_count(2'(channel), 8'd8);
				if(channel == error_channel) begin
					read.expect_flag( 2'(channel), SE); // expect SE flag
				end
				else begin
					read.expect_flags( 2'(channel), expected_flags);
					read.expect_packet(2'(channel), packets[channel]);
				end
			end
		end
		get_checker_config().expect_CRM_symbol_coding_error_in_dsi_packet = 'b0;
		#100us;
	endtask
endclass