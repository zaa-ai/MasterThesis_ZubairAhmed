class pdcm_long_packets_end_at_receive_timeout_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(pdcm_long_packets_end_at_receive_timeout_seq)

	function new(string name = "");
		super.new("pdcm_long_packets_end_at_receive_timeout");
	endfunction
	
	task run_tests();
		log_sim_description("receive packets with 255 symbols at receive timeout", LOG_LEVEL_SEQUENCE);
		get_checker_config().disable_all_master_transmission_checkers();
		
		for(int period = 2250; period < 2411; period += 10) begin
			log_sim_description($sformatf("receive packets with 255 symbols at receive timeout and PDCM period of %0dus", period), LOG_LEVEL_OTHERS);
			
			for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
				tdma_scheme_pdcm scheme;
				dsi3_pdcm_packet packet = new();
				if(!packet.randomize() with {data.size() == 255; source_id_symbols == dsi3_pkg::SID_8Bit;}) `uvm_error(this.get_name(), "randomization error")						
				scheme = tdma_scheme_pdcm_factory::single_pdcm_packet(packet);
				scheme.packets[0].tolerance_int = 1000;
				scheme.set_source_id_for_all_packets(dsi3_pkg::SID_8Bit);
				scheme.pdcm_period = period;
				scheme.packets[0].set_start_time_window(20, 50);

				`upload_tdma_scheme_with(scheme, channels == 2'b01 << channel;)
				
				scheme.packets[0].set_start_time_window(25, 25);
				add_slave_pdcm_scheme(channel, scheme);
				
				`spi_frame_begin
					`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b01 << channel; pulse_count == 1;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				wait_for_dab(3ms, 1'b1);
				
				begin
					int symbol_count;
					int words;
					dsi_response_flags expected_flags[$] = {};
					dsi_response_flags ignored_flags[$]  = {};
					spi_read_pdcm_frame_seq read;
					
					`spi_frame_begin
						`spi_frame_send(read, channel_bits == 2'b01 << channel;)
						`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
					`spi_frame_end
					
					symbol_count = int'(read.get_symbol_count(channel, 0));
					if(symbol_count != 255) begin
						expected_flags.push_back(SCE);
						expected_flags.push_back(TE);
					end
					else if(period >= 2340 && period <= 2360) begin
						// there is a window where symbol_count == 255 but TE is set too (packet end has not been detected by receiver)
						ignored_flags.push_back(TE);
					end
					
					if(symbol_count != 255 || packet.crc_correct == 1'b0) begin
						expected_flags.push_back(CRC);
					end
					read.expect_flags(2'(channel), 0, expected_flags, ignored_flags);
					words = symbol_count / 4;
					for(int i=0; i < words; i++) begin
						read.expect_packet_data(2'(channel), 0, i, packet.get_word(i));
					end
				end
			end
		end
		get_checker_config().enable_all_master_transmission_checkers();
		#1ms;
	endtask
endclass
