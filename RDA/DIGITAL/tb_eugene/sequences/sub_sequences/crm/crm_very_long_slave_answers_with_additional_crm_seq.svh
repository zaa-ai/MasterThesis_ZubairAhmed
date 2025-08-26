class crm_very_long_slave_answers_with_additional_crm_seq extends base_dsi_master_seq;

	`uvm_object_utils(crm_very_long_slave_answers_with_additional_crm_seq)
	
	function new(string name = "");
		super.new("crm_very_long_slave_answers_with_additional_crm");
	endfunction : new
	
	virtual task run_tests();
		dsi3_packet packets[project_pkg::DSI_CHANNELS-1:0];
		log_sim_description("receive very long slave answer and additional CRM", LOG_LEVEL_SEQUENCE);
		get_checker_config().disable_all_master_transmission_checkers();
			
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			spi_read_crm_data_packets_seq read_1, read_2;
			int symbol_count;
			random_slave_scheme_for_channel(channel, 310, 250, 300, 3, packets);
			add_slave_crm_scheme(channel, tdma_scheme_crm::no_answer());
			
			check_dab(1'b1);
			`spi_frame_begin
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b01 << channel; broad_cast == 1'b0;)
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b01 << channel; broad_cast == 1'b0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#3ms;
			check_dab(1'b0);
		
			`spi_frame_begin
				`spi_frame_send(read_1, channel_bits == 2'b01 << channel;)
				`spi_frame_send(read_2, channel_bits == 2'b01 << channel;)
				`spi_frame_create(spi_tx_crc_request_seq,)
			`spi_frame_end
			check_dab(1'b1);
			
			symbol_count = packets[channel].data.size();
			
			
			if(read_1.get_symbol_count(2'(channel)) < 8) `uvm_error(this.get_type_name(), $sformatf("Unexpected symbol count at channel %0d, expected more than 8 symbols, got %0d!", channel, read_1.get_symbol_count(2'(channel))))
			read_1.expect_flags( 2'(channel), {CRC, SCE, TE});
			read_1.expect_packet_data(2'(channel), 0, packets[channel].get_word(0));
			read_1.expect_packet_data(2'(channel), 1, packets[channel].get_word(1));
			
			if(read_2.get_symbol_count(2'(channel)) < 8) `uvm_error(this.get_type_name(), $sformatf("Unexpected symbol count at channel %0d, expected more than 8 symbols, got %0d!", channel, read_2.get_symbol_count(2'(channel))))
			read_2.expect_flags( 2'(channel), {CRC, SCE, TE}, {SE}); // ignore symbol coding errors
		end
		#100us;
		get_checker_config().enable_all_master_transmission_checkers();
	endtask
endclass