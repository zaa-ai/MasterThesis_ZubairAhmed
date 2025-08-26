class pdcm_short_inter_packet_gaps_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(pdcm_short_inter_packet_gaps_seq)

	function new(string name = "");
		super.new("pdcm_short_inter_packet_gaps");
	endfunction
	
	task run_tests();
		spi_read_pdcm_frame_seq read;
		chip_times_iterator_with_register_model chip_iterator = new(regmodel);
		
		log_sim_description("receive packets with short inter packet separation time", LOG_LEVEL_SEQUENCE);
		
		while(chip_iterator.has_next()) begin
			int chip_time = chip_iterator.get_current();
			chip_iterator.apply_next();
			
			for(int chip_times_ips = 7; chip_times_ips > 4; chip_times_ips--) begin
				for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
					int next_start;
					dsi3_pdcm_packet packet_1 = new();
					dsi3_pdcm_packet packet_2 = new();
					tdma_scheme_packet_pdcm scheme_packet_2;
					tdma_scheme_pdcm scheme;
					
					log_sim_description($sformatf("receive packets with inter packet time of %0d x %0dus chiptime at channel %0d", chip_times_ips,chip_time, channel), LOG_LEVEL_OTHERS);
					
					if(!packet_1.randomize() with {data.size() == 8; source_id_symbols == 2'd2;}) `uvm_error(this.get_name(), "randomization error")
					if(!packet_2.randomize() with {data.size() == 8; source_id_symbols == 2'd2;}) `uvm_error(this.get_name(), "randomization error")
					
					scheme = tdma_scheme_pdcm_factory::single_pdcm_packet(packet_1, chip_time);
					scheme.packets[0].tolerance_int = 1000;
					scheme.packets[0].earliest_start_time = 25;
					scheme.packets[0].latest_start_time = 26;
					
					next_start = 25 + 3 * chip_time * 8 + chip_times_ips * chip_time;
					scheme_packet_2 = tdma_scheme_packet_pdcm::new_packet(next_start, next_start+1, 8, dsi3_pkg::SID_8Bit);
					scheme_packet_2.packet = packet_2;
					scheme.add_packet(scheme_packet_2);
					scheme.pdcm_period = 500;
					
					`upload_tdma_scheme_with(scheme, channels == 2'b01 << channel;)
					scheme.packets[0].latest_start_time = 25;
					scheme.packets[1].latest_start_time = next_start;
					
					add_slave_pdcm_scheme(channel, scheme);
					#50us;
	
					`spi_frame_begin
						`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b01 << channel; pulse_count == 1;)
						`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
					`spi_frame_end
					#(scheme.pdcm_period * 1us);
					`spi_frame_begin
						`spi_frame_send(read, channel_bits == 2'b01 << channel;)
						`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
					`spi_frame_end
					#100us;					
				end
			end
		end
		chip_iterator.apply_default();
		#1ms;
	endtask
endclass
