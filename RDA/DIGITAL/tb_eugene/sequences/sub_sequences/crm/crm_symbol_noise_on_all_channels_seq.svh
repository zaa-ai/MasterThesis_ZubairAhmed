class crm_symbol_noise_on_all_channels_seq extends base_dsi_master_seq;

	`uvm_object_utils(crm_symbol_noise_on_all_channels_seq)
	
	function new(string name = "");
		super.new("crm_symbol_noise_on_all_channels");
	endfunction : new
	
	virtual task run_tests();
		log_sim_description("CRM and symbol noise on all channels", LOG_LEVEL_SEQUENCE);
		
		for(int noise_symbols=1; noise_symbols < 4; noise_symbols++) begin
			spi_read_crm_data_packets_seq read;
			dsi3_crm_packet packets[$];
			
			log_sim_description($sformatf("CRM and %0d symbols noise on all channels", noise_symbols), LOG_LEVEL_OTHERS);
			for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
				tdma_scheme scheme;
				
				dsi3_crm_packet next_packet = new();
				if(!next_packet.randomize()) `uvm_error(this.get_name(), "randomization error")
				packets.push_back(next_packet);
				
				scheme = tdma_scheme_crm::valid_with_data(next_packet.get_word(0), next_packet.get_word(1));
				scheme.packets[0].set_start_time_window(305, 310);
				// add some noise
				scheme.packets.push_front(create_crm_noise_packet(noise_symbols));
				
				add_slave_crm_scheme(channel, scheme);
			end
			
			`spi_frame_begin
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#500us;
			
			`spi_frame_begin
				`spi_frame_send(read, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			// check results
			for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
				read.expect_flags(2'(channel), packets[channel].crc_correct ? {} : {CRC});
				read.expect_packet(2'(channel), packets[channel]);
			end
			`spi_frame_begin
				`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; crm_buffer == 1'b1;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#50us;
		end
		#100us;
	endtask
endclass