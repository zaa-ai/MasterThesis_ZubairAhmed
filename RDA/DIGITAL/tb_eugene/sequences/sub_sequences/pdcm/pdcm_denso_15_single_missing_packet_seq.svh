class pdcm_denso_15_single_missing_packet_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(pdcm_denso_15_single_missing_packet_seq)
	
	function new(string name = "");
		super.new("pdcm_denso_15_single_missing_packet");
	endfunction
	
	virtual task run_tests();
		tdma_scheme_pdcm_denso_15 scheme = new();

		log_sim_description("PDCM with one single missing packet on all channels", LOG_LEVEL_SEQUENCE);
		
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)	
		check_dab(1'b1);
		
		for (int missing_packet_index = 0; missing_packet_index < scheme.packets.size(); missing_packet_index++) begin
			tdma_scheme_pdcm_denso_15 missing_packet_scheme = new();
			
			log_sim_description($sformatf("PDCM with packet at index %0d missing", missing_packet_index), LOG_LEVEL_OTHERS);
			
			missing_packet_scheme.packets[missing_packet_index].enable = 1'b0;
			set_tdma_scheme_pdcm(0, missing_packet_scheme);
			set_tdma_scheme_pdcm(1, missing_packet_scheme);
			
			`spi_frame_begin
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 8'd1;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#(scheme.pdcm_period * 1us);
			check_dab(1'b0);
			
			`spi_frame_begin
				`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11; )
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			check_dab(1'b1);
			#100us;
		end
	endtask
endclass