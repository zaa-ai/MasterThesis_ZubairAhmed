class pdcm_symbol_coding_error_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(pdcm_symbol_coding_error_seq)

	function new(string name = "");
		super.new("pdcm_symbol_coding_error");
	endfunction
	
	task run_tests();
		tdma_scheme_pdcm_denso_15 scheme = new();
		log_sim_description("receive packets with symbol coding error (SE) on all channels", LOG_LEVEL_SEQUENCE);

		get_checker_config().expect_PDCM_symbol_coding_error_in_dsi_packet[0] = {};
		get_checker_config().expect_PDCM_symbol_coding_error_in_dsi_packet[1] = {};

		`upload_tdma_scheme_with(scheme, channels == 2'b11;)
		#50us;
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			foreach (scheme.packets[packet_index]) begin
				log_sim_description($sformatf("symbol coding error in channel %0d at packet index %0d", channel, packet_index), LOG_LEVEL_OTHERS);
				
				set_symbol_coding_error(scheme, packet_index);
				set_tdma_scheme_pdcm(channel, scheme);
				
				get_checker_config().expect_PDCM_symbol_coding_error_in_dsi_packet[channel] = {packet_index};
				
				`spi_frame_begin
					`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b01 << channel; pulse_count == 1;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				
				#(scheme.pdcm_period * 1us);

				`spi_frame_begin
					`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b01 << channel;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				#100us;
			end
		end
		get_checker_config().expect_PDCM_symbol_coding_error_in_dsi_packet[0] = {};
		get_checker_config().expect_PDCM_symbol_coding_error_in_dsi_packet[1] = {};
		#500us;
	endtask
	
	function void set_symbol_coding_error(tdma_scheme_pdcm scheme, int packet_index);
		foreach (scheme.packets[i]) begin
			scheme.packets[i].symbol_coding_error_injection = (i == packet_index) ? common_env_pkg::ALWAYS_ERROR : common_env_pkg::NEVER_ERROR; // inject SE
			// tolerance
			scheme.packets[i].tolerance_int_min = 1000;
			scheme.packets[i].tolerance_int_max = 1000;
		end
	endfunction
endclass
