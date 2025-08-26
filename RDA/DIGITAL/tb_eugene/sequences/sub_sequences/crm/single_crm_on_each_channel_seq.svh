class single_crm_on_each_channel_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(single_crm_on_each_channel_seq)

	function new(string name = "");
		super.new("single_crm_on_each_channel");
	endfunction
	
	task run_tests();
		dsi3_crm_packet packets[$];
		
		log_sim_description("single CRM TRANSMIT on each channel within one frame", LOG_LEVEL_SEQUENCE);

		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			dsi3_crm_packet next_packet = new();
			if(!next_packet.randomize()) `uvm_error(this.get_name(), "randomization error")
			packets.push_back(next_packet);
			add_slave_crm_scheme(channel, tdma_scheme_crm::valid_with_data(next_packet.get_word(0), next_packet.get_word(1)));
		end
		
		check_dab(1'b1);
		`spi_frame_begin
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b01; broad_cast == 0;)
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b10; broad_cast == 0;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#500us;
		check_dab(1'b0);
		
		// check results
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			spi_read_crm_data_packets_seq read_seq;

			`spi_frame_begin
				`spi_frame_send(read_seq, channel_bits == 2'(1 << channel);)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			if(channel < project_pkg::DSI_CHANNELS - 1) check_dab(1'b0);
			
			read_seq.expect_flags(2'(channel),  packets[channel].crc_correct ? {} : {CRC});
			read_seq.expect_packet(2'(channel), packets[channel]);
		end
		check_dab(1'b1);
		#100us;
	endtask
endclass
