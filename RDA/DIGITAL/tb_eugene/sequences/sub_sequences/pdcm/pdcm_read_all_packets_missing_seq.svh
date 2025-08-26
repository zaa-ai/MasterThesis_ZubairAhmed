class pdcm_read_all_packets_missing_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(pdcm_read_all_packets_missing_seq)

	function new(string name = "");
		super.new("pdcm_read_all_packets_missing");
	endfunction
	
	task run_tests();
		// clear PDCM data from buffer
		`spi_frame_begin
			`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; pdcm_buffer == 1'b1;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end

		log_sim_description($sformatf("Read PDCM without any slave answer (all packets are missing) on all channels"), LOG_LEVEL_SEQUENCE);
		
		for (int packet_count = 1; packet_count < 16; packet_count++) begin
			tdma_scheme_pdcm scheme = new();
			
			log_sim_description($sformatf("Read PDCM without any slave answer for a TDMA scheme with %0d packets on all channels", packet_count), LOG_LEVEL_OTHERS);
			
			if(!scheme.randomize() with {packets.size() == packet_count; symbol_count_max <=16; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
			`upload_tdma_scheme_with(scheme, channels == 2'b11;)
			check_dab(1'b1);
			
			// disable all packets in this scheme
			foreach(scheme.packets[i]) begin
				scheme.packets[i].enable = 1'b0;
			end
			set_tdma_scheme_pdcm(0, scheme);
			set_tdma_scheme_pdcm(1, scheme);
			
			`spi_frame_begin
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 8'd1;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#(scheme.pdcm_period * 1us);
			check_dab(1'b0);
			`spi_frame_begin
				`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#100us;
			check_dab(1'b1);
		end
	endtask
endclass