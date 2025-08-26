class crm_transmit_and_read_in_one_frame_seq extends base_dsi_master_seq;

	`uvm_object_utils(crm_transmit_and_read_in_one_frame_seq)
	
	function new(string name = "");
		super.new("crm_transmit_and_read_in_one_frame");
	endfunction : new
	
	virtual task run_tests();
		spi_read_crm_data_packets_seq read_seq;
		dsi3_crm_packet packets[3:0][$];
		int crm_count = 5;
		
		log_sim_description("CRM transmit and read data within one frame", LOG_LEVEL_SEQUENCE);
	
		for (int i=0; i < crm_count; i++) begin
			for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
				dsi3_crm_packet next_packet = new();
				if(!next_packet.randomize()) `uvm_error(this.get_name(), "randomization error")
				packets[channel].push_back(next_packet);
				add_slave_crm_scheme(channel, tdma_scheme_crm::valid_with_data(next_packet.get_word(0), next_packet.get_word(1)));
			end
		end
		
		`spi_frame_begin
			`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; crm_buffer == 1'b1;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		for (int i=0; i < crm_count; i++) begin
			check_dab((i==0) ? 1'b1 : 1'b0);
			`spi_frame_begin
				// start CRM and read data
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 0;)
				`spi_frame_send(read_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1; mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#500us;
			check_dab(1'b0);
		
			for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
				if(i==0) begin
					read_seq.expect_empty(2'(channel));
				end 
				else begin
					read_seq.expect_flags( 2'(channel), packets[channel][i-1].crc_correct ? {} : {CRC});
					read_seq.expect_packet(2'(channel), packets[channel][i-1]);
				end
			end
		end
		check_dab(1'b0);
		
		`spi_frame_begin
			// clear buffer and read data in one frame
			`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; crm_buffer == 1'b1;)
			`spi_frame_send(read_seq, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			read_seq.expect_flags( 2'(channel), packets[channel][$].crc_correct ? {} : {CRC});
			read_seq.expect_packet(2'(channel), packets[channel][$]);
		end
		
		#100us;
	endtask
endclass