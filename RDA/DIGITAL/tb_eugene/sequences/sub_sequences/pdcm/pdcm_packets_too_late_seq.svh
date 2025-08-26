class pdcm_packets_too_late_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(pdcm_packets_too_late_seq)

	function new(string name = "");
		super.new("pdcm_packets_too_late");
	endfunction 
	
	task run_tests();
		tdma_scheme_pdcm scheme = new();
		int start_time = 200;
		dsi3_pdcm_packet packets[3:0][$];
			
		log_sim_description("packets from slave are too late", LOG_LEVEL_SEQUENCE);
		get_checker_config().disable_all_master_transmission_checkers();
		
		repeat(3) begin
			for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
				dsi3_pdcm_packet packet = new();
				tdma_scheme scheme;
				if(!packet.randomize() with {data.size() == 8; source_id_symbols == dsi3_pkg::SID_8Bit;}) `uvm_error(this.get_name(), "randomization error")						
				packets[channel].push_back(packet);
				scheme = tdma_scheme_pdcm_factory::single_pdcm_packet(packet);
				scheme.packets[0].earliest_start_time = start_time;
				scheme.packets[0].latest_start_time = start_time + 5;
				add_slave_pdcm_scheme(channel, scheme);
				start_time += 10;
			end
		end
		
		if(!scheme.randomize() with {packets.size() == 1; symbol_count_min == 8; symbol_count_max == 8; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		scheme.packets[0].id_symbol_count = dsi3_pkg::SID_8Bit;
		scheme.pdcm_period = 300;
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)
		#50us;		
		`spi_frame_begin
			`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 3;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#1ms;
		
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
		
			for(int period_index=0; period_index < 3; period_index++) begin
				spi_read_pdcm_frame_seq read;
				spi_pdcm_frame_header frame_header;
				
				`spi_frame_begin
					`spi_frame_send(read, channel_bits == 2'b01 << channel;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				
				frame_header = read.get_frame_header(2'(channel));
				if(frame_header.packet_count == 8'd1) begin
					int symbol_count = int'(read.get_symbol_count(2'(channel), 0));
				
					if(read.has_flag(2'(channel), 0, SE)) begin
						// stop checking if there is a SE flag (rest of data is corrupted)	
						break;
					end
					else begin
						logic[31:0] mask = common_env_pkg::create_symbol_mask(symbol_count);
						dsi_response_flags expected_flags[$] = {TE};
						dsi3_pdcm_packet next_packet = packets[channel][period_index];
						if((symbol_count > 0) && (next_packet.crc_correct == 1'b0 || symbol_count < 8)) expected_flags.push_back(CRC);
						if(symbol_count != 8) expected_flags.push_back(SCE);
	
						read.expect_flags(2'(channel), 0, expected_flags);
						read.expect_packet_data(2'(channel), 0, 0, next_packet.get_word(0) & mask[31:16]);
						read.expect_packet_data(2'(channel), 0, 1, next_packet.get_word(1) & mask[15:0]);
					end
				end
				else if(frame_header.packet_count == 8'd0) begin
					read.expect_empty_data(2'(channel), 0, {SCE});
				end
				else begin
					`uvm_error(get_type_name(), $sformatf("unexpected packet count in frame header, expected 1 or 0, got %0d", frame_header.packet_count))
				end
			end
		end
		`spi_frame_begin
			`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; crm_buffer == 1'b0; pdcm_buffer == 1'b1;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#1ms;
		get_checker_config().enable_all_master_transmission_checkers();
	endtask
endclass
