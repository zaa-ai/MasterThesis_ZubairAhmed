class crm_two_short_slave_answers_seq extends base_dsi_master_seq;

	`uvm_object_utils(crm_two_short_slave_answers_seq)
	
	function new(string name = "");
		super.new("crm_two_short_slave_answers");
	endfunction : new
	
	virtual task run_tests();
		dsi3_packet packets[project_pkg::DSI_CHANNELS-1:0];
		log_sim_description("receive two short slave answers in one CRM", LOG_LEVEL_SEQUENCE);
			
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			spi_read_crm_data_packets_seq read;
			random_slave_scheme_for_channel(channel, 265, 4, 4, 3, packets);

			`spi_frame_begin
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b01 << channel; broad_cast == 1'b0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#340us;
			send_slave_answer(channel);
			#300us;
		
			`spi_frame_begin
				`spi_frame_send(read, channel_bits == 2'b01 << channel;)
				`spi_frame_create(spi_tx_crc_request_seq,)
			`spi_frame_end
			
			read.expect_flags( 2'(channel), {TE, SCE, CRC});
			read.expect_packet(2'(channel), packets[channel], 1'b1);
			
			// read again
			`spi_frame_begin
				`spi_frame_send(read, channel_bits == 2'b01 << channel;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			read.expect_empty(channel);
			
			`spi_frame_begin
				`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'(1<<channel); crm_buffer == 1'b1;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
		end
		#100us;
	endtask
	
	task send_slave_answer(int channel);
		dsi3_slave_tr disturbance;
		dsi3_slave_sequencer_t seq = get_slave_agent(channel).m_sequencer;
		`uvm_do_on_with(disturbance, seq, {
				msg_type == dsi3_pkg::CRM; 
				data.size() == 8;
				chips_per_symbol == 3; 
				chiptime == 3; 
				symbol_coding_error_injection == NEVER_ERROR;
				chip_length_error_injection == NEVER_ERROR;})
	endtask
endclass