class pdcm_clock_ref_error_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(pdcm_clock_ref_error_seq)

	function new(string name = "");
		super.new("pdcm_clock_ref_error");
	endfunction : new
	
	task run_tests();
		int frequency = 500_000;
		tdma_scheme_pdcm scheme = new();
		log_sim_description("receive packets with clock error (CE) on all channels", LOG_LEVEL_SEQUENCE);
		
		if(!scheme.randomize() with {packets.size() == 15; symbol_count_min == 32; symbol_count_max == 32; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		
		get_checker_config().expect_PDCM_clock_ref_error_in_dsi_packet[0] = {};
		get_checker_config().expect_PDCM_clock_ref_error_in_dsi_packet[1] = {};
		
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)
		
		// make sure all packets start at the same time
		foreach (scheme.packets[packet_index]) begin
			shortint unsigned earliest = scheme.packets[packet_index].earliest_start_time;
			shortint unsigned latest = scheme.packets[packet_index].latest_start_time;
			int medium_start = earliest + (latest-earliest)/2;
			scheme.packets[packet_index].latest_start_time = medium_start;
			scheme.packets[packet_index].earliest_start_time = medium_start;
		end
		
		set_tdma_scheme_pdcm(0, scheme);
		set_tdma_scheme_pdcm(1, scheme);
		#50us;
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			foreach (scheme.packets[packet_index]) begin
				log_sim_description($sformatf("clock error in channel %0d at packet index %0d", channel, packet_index), LOG_LEVEL_OTHERS);
				
				get_checker_config().expect_PDCM_clock_ref_error_in_dsi_packet[channel] = {packet_index};
				
				`spi_frame_begin
					`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b01 << channel; pulse_count == 1;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				fork
					begin
						#(scheme.pdcm_period * 1us);
					end
					begin
						time delay_after_pulse = scheme.packets[packet_index].get_earliest_start_time() - 16us;
						@(negedge m_dsi3_master_agent[channel].m_config.vif.cable.Voltage);
						#delay_after_pulse;
						set_clk_ref(frequency * 0.75);
						#10us;
						set_clk_ref(frequency);
					end
				join

				`spi_frame_begin
					`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b01 << channel;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				#100us;
			end
		end
		get_checker_config().expect_PDCM_clock_ref_error_in_dsi_packet[0] = {};
		get_checker_config().expect_PDCM_clock_ref_error_in_dsi_packet[1] = {};
		#500us;
	endtask
endclass
