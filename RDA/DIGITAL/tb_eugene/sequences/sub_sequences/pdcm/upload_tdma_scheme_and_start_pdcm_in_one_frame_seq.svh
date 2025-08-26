class upload_tdma_scheme_and_start_pdcm_in_one_frame_seq extends base_dsi_master_seq;

	`uvm_object_utils(upload_tdma_scheme_and_start_pdcm_in_one_frame_seq)
	
	function new(string name = "");
		super.new("upload_tdma_scheme_and_start_pdcm_in_one_frame");
	endfunction : new
	
	virtual task run_tests();
		tdma_scheme_pdcm_denso_15 scheme = new();
		
		log_sim_description("Upload TDMA scheme and start PDCM in one SPI frame", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		set_tdma_scheme_pdcm(0, scheme);
		set_tdma_scheme_pdcm(1, scheme);
		
		`spi_frame_begin
			foreach (scheme.packets[i]) begin
				`spi_frame_create(spi_upload_tdma_packet_seq,
					channel_bits == 2'b11;
					packet_index == 4'(i);
					tdma_packet.earliest_start_time == scheme.packets[i].earliest_start_time;
					tdma_packet.latest_start_time 	== scheme.packets[i].latest_start_time;
					tdma_packet.id_symbol_count		== scheme.packets[i].id_symbol_count;
					tdma_packet.symbol_count 		== scheme.packets[i].symbol_count;)
			end
			`spi_frame_create(spi_validate_tdma_scheme_seq, channel_bits == 2'b11; packet_count == 4'(scheme.packets.size); pdcm_period == 16'(scheme.pdcm_period);)
			// sync is needed!!!
			`spi_frame_create(spi_sync_dsi_channels_seq, channel_bits == 2'b11; external_sync == 1'b0;)
			`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 8'd1;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		#100us;
		transaction_recorder.expect_tr_count_for_all_channels(1);
		#(scheme.pdcm_period * 1us);
	
		`spi_frame_begin
			`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		transaction_recorder.disable_recorder();
		#100us;
	endtask
	
endclass
