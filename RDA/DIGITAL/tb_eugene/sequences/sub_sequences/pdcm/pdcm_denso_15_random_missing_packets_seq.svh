class pdcm_denso_15_random_missing_packets_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(pdcm_denso_15_random_missing_packets_seq)
	
	rand logic[15:0] packets_enable;
	
	function new(string name = "");
		super.new("pdcm_denso_15_random_missing_packets");
	endfunction
	
	virtual task run_tests();
		tdma_scheme_pdcm_denso_15 scheme = new();
			tdma_scheme_pdcm_denso_15 missing_packets_scheme = new();

		log_sim_description($sformatf("PDCM with multiple random missing packets: 0b%b on all channels", packets_enable), LOG_LEVEL_OTHERS);
		
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)	
		check_dab(1'b1);
		
		foreach(missing_packets_scheme.packets[i]) begin
			missing_packets_scheme.packets[i].enable = packets_enable[i];
		end
		
		set_tdma_scheme_pdcm(0, missing_packets_scheme);
		set_tdma_scheme_pdcm(1, missing_packets_scheme);
			
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
	endtask
endclass