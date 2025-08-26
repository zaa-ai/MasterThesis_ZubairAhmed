class crm_read_data_using_multiple_tx_crc_seq extends base_dsi_master_seq;

	`uvm_object_utils(crm_read_data_using_multiple_tx_crc_seq)
	
	function new(string name = "");
		super.new("crm_read_data_using_multiple_tx_crc");
	endfunction : new
	
	virtual task run_tests();
		dsi3_crm_packet packets[$];
		spi_read_crm_data_packets_seq reads[$];
		spi_tx_crc_request_seq tx_crcs[$];
		
		log_sim_description("CRM and read data using multiple TX CRCs", LOG_LEVEL_SEQUENCE);
		
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			dsi3_crm_packet packet = new();
			if(!packet.randomize()) `uvm_error(this.get_name(), "randomization error")	
			packets.push_back(packet);
			
			add_slave_crm_scheme(channel, tdma_scheme_crm::valid_with_data(packet.get_word(0), packet.get_word(1)));
			`spi_frame_begin
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b01 << channel; broad_cast == 1'b0; dsi3_crc_correct == 1'b1;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#500us;
		end
		
		`spi_frame_begin
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			`spi_frame_send(reads[channel], channel_bits == 2'b01 << channel;)
			`spi_frame_send(tx_crcs[channel], mosi_crc_correct == 1'b1;)
		end
		`spi_frame_end
	
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			reads[channel].expect_flags(2'(channel), packets[channel].crc_correct ? {} : {CRC});
			reads[channel].expect_packet(2'(channel), packets[channel]);
		end
	endtask
endclass