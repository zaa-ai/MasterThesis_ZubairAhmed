class crm_wrong_symbol_counts_seq extends base_dsi_master_seq;

	`uvm_object_utils(crm_wrong_symbol_counts_seq)
	
	function new(string name = "");
		super.new("crm_wrong_symbol_counts");
	endfunction : new
	
	virtual task run_tests();
		spi_read_crm_data_packets_seq read;
		
		log_sim_description("receive symbol counts != 8", LOG_LEVEL_SEQUENCE);
		
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			for(int symbol_count = 1; symbol_count <= 12; symbol_count++) begin
				dsi_response_flags expected_flags[$];
				tdma_scheme scheme = new("crm_scheme");
				tdma_scheme_packet scheme_packet = create_crm_noise_packet(symbol_count); 
				scheme.add_packet(scheme_packet);
				add_slave_crm_scheme(channel, scheme);
				
				log_sim_description($sformatf("receive %0d symbols at channel %0d", symbol_count, channel), LOG_LEVEL_OTHERS);
				
				`spi_frame_begin
					`spi_frame_create(spi_crm_seq, channel_bits == 2'b01 << channel; broad_cast == 1'b0; dsi3_crc_correct == 1'b1;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				#500us;
				
				check_dab(1'b0);
	
				`spi_frame_begin
					`spi_frame_send(read, channel_bits == 2'b01 << channel;)
					`spi_frame_create(spi_tx_crc_request_seq,)
				`spi_frame_end
				
				if(symbol_count >= 4) begin
					expected_flags = {CRC, TE};
					if(symbol_count != 8) expected_flags.push_back(SCE);
					read.expect_flags(2'(channel), expected_flags);
					read.expect_symbol_count(2'(channel), 8'(symbol_count));
					read.expect_packet_data(2'(channel), 0, scheme_packet.packet.get_word(0));
					read.expect_packet_data(2'(channel), 1, (symbol_count > 4) ? scheme_packet.packet.get_word(1) : 16'h0000);
				end
				else begin
					read.expect_empty_data(2'(channel), {SCE});
				end
				#100us;
			end
		end
	endtask
endclass