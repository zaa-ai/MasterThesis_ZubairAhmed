class crm_random_on_different_channels_seq extends base_dsi_master_seq;

	`uvm_object_utils(crm_random_on_different_channels_seq)

	function new(string name = "");
		super.new("crm_random_on_different_channels");
	endfunction : new

	
	virtual task run_tests();
		log_sim_description("CRM TRANSMIT on random channel", LOG_LEVEL_SEQUENCE);
		
		// clear data from buffer
		`spi_frame_begin
			`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; crm_buffer == 1'b1;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		repeat(20) begin
			crm_channel_random();
		end
	endtask

	task crm_channel_random();
		spi_read_crm_data_packets_seq read[project_pkg::DSI_CHANNELS-1:0];
		dsi3_crm_packet packets[$];
		
		logic [project_pkg::DSI_CHANNELS-1:0] aktiv_channel;

		aktiv_channel = 2'($urandom_range(3,1));
			
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			dsi3_crm_packet next_packet = new();
			if(!next_packet.randomize()) `uvm_error(this.get_name(), "randomization error")
			packets.push_back(next_packet);
			if (aktiv_channel[channel]) begin
				add_slave_crm_scheme(channel, tdma_scheme_crm::valid_with_data(next_packet.get_word(0), next_packet.get_word(1)));
			end
		end

		// create spi command on active channel
		`spi_frame_begin
			for (int channel = 0; channel < project_pkg::DSI_CHANNELS; channel++) begin
				if (aktiv_channel[channel]) begin
					 `spi_frame_create(spi_crm_seq, channel_bits == 2'h1 << channel; broad_cast == 0;)
				end
			end
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end

		#500us;

		// read data from active channel
		`spi_frame_begin
			for (int channel = 0; channel < project_pkg::DSI_CHANNELS; channel++) begin
				if (aktiv_channel[channel]) begin
					`spi_frame_send(read[channel], channel_bits == (2'h1<<channel);)
				end
			end
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end

		// check results
		for (int channel = 0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			if (aktiv_channel[channel]) begin
				read[channel].expect_flags(channel[1:0], packets[channel].crc_correct ? {} : {CRC});
				read[channel].expect_packet(channel[1:0], packets[channel]);
			end
		end
		#100us;
	endtask

endclass