class pdcm_denso_one_missing_and_one_too_large_packet_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(pdcm_denso_one_missing_and_one_too_large_packet_seq)
	
	function new(string name = "");
		super.new("pdcm_denso_one_missing_and_one_too_large_packet");
	endfunction
	
	virtual task run_tests();
		tdma_scheme_pdcm_denso scheme = new();

		log_sim_description("PDCM with packet n missing and too large packet n-1", LOG_LEVEL_SEQUENCE);
		
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)	
		check_dab(1'b1);
		
		for (int packet_index = 1; packet_index < scheme.packets.size(); packet_index++) begin
			tdma_scheme_pdcm_denso modified_scheme = new();
			
			log_sim_description($sformatf("PDCM with missing packet at index %0d and too large packet at index %0d", packet_index, packet_index-1), LOG_LEVEL_OTHERS);
			
			modified_scheme.packets[packet_index-1].symbol_count = 8'd24;
			modified_scheme.packets[packet_index].enable = 1'b0;
			set_tdma_scheme_pdcm(0, modified_scheme);
			set_tdma_scheme_pdcm(1, modified_scheme);
			
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