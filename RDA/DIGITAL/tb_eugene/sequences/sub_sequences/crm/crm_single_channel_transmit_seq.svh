class crm_single_channel_transmit_seq extends base_dsi_master_seq;

	`uvm_object_utils(crm_single_channel_transmit_seq)

	function new(string name = "");
		super.new("crm_single_channel_transmit");
	endfunction : new

	virtual task run_tests();
		spi_read_crm_data_packets_seq read;
		spi_crm_seq crm_seq;
		
		log_sim_description("single CRM transmit and read data", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			dsi3_crm_packet packet = new();
			if(!packet.randomize()) `uvm_error(this.get_name(), "randomization error")	
			
			log_sim_description($sformatf("single CRM transmit and read data at channel %0d", channel), LOG_LEVEL_OTHERS);
			transaction_recorder.clear_all();
			
			add_slave_crm_scheme(channel, tdma_scheme_crm::valid_with_data(packet.get_word(0), packet.get_word(1)));
			check_dab(1'b1);
			`spi_frame_begin
				`spi_frame_send(crm_seq, channel_bits == 2'b01 << channel; broad_cast == 1'b0; dsi3_crc_correct == 1'b1;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#500us;
			check_dab(1'b0);
			`spi_frame_begin
				`spi_frame_send(read, channel_bits == 2'b01 << channel;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			check_dab(1'b1);
			
			// check results
			transaction_recorder.expect_packets(channel, {crm_seq.crm_packet});

			read.expect_flags(2'(channel), packet.crc_correct ? {} : {CRC});
			read.expect_symbol_count(2'(channel), 8'd8);
			read.expect_packet(2'(channel), packet);
			#100us;
		end
	endtask
endclass