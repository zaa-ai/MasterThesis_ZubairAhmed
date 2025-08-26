class crm_very_long_slave_answers_seq extends base_dsi_master_seq;

	`uvm_object_utils(crm_very_long_slave_answers_seq)
	
	function new(string name = "");
		super.new("crm_very_long_slave_answers");
	endfunction : new
	
	virtual task run_tests();
		dsi3_packet packets[project_pkg::DSI_CHANNELS-1:0];
		log_sim_description("receive very long slave answers in CRM", LOG_LEVEL_SEQUENCE);
		get_checker_config().disable_all_master_transmission_checkers();
			
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			spi_read_crm_data_packets_seq read;
			random_slave_scheme_for_channel(channel, 310, 250, 300, 3, packets);
			
			check_dab(1'b1);
			`spi_frame_begin
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b01 << channel; broad_cast == 1'b0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#3500us;
			check_dab(1'b0);
		
			`spi_frame_begin
				`spi_frame_send(read, channel_bits == 2'b01 << channel;)
				`spi_frame_create(spi_tx_crc_request_seq,)
			`spi_frame_end
			check_dab(1'b1);
			
			read.expect_flags( 2'(channel), {CRC, SCE, TE});
			read.expect_packet_data(2'(channel), 0, packets[channel].get_word(0));
			read.expect_packet_data(2'(channel), 1, packets[channel].get_word(1));
		end
		#100us;
		get_checker_config().enable_all_master_transmission_checkers();
	endtask
endclass