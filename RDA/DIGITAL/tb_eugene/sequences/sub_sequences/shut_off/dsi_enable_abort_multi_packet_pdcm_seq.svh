class dsi_enable_abort_multi_packet_pdcm_seq extends base_dsi_master_seq;

	`uvm_object_utils(dsi_enable_abort_multi_packet_pdcm_seq) 
    
	function new(string name = "");
		super.new("dsi_enable_abort_multi_packet_pdcm");
	endfunction

	virtual task run_tests();
		tdma_scheme_pdcm_denso scheme_0 = new();
		tdma_scheme_pdcm_denso scheme_1 = new();
		
		log_sim_description("abort multi packet PDCM (Denso scheme) using DSI_ENABLE register", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		`upload_tdma_scheme_with(scheme_0, channels == 2'b11;)
		set_tdma_scheme_pdcm(0, scheme_0);
		set_tdma_scheme_pdcm(1, scheme_1);
		
		repeat(10) begin
			int abort_delay = $urandom_range(scheme_0.pdcm_period, 0);
			int abort_duration = $urandom_range(300, 1);
			transaction_recorder.clear_all();
			
			`spi_frame_begin
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 8'd3;)
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)	 // will be ignored
				`spi_frame_create(spi_discovery_mode_seq, channel_bits == 2'b11;)			 // will be ignored
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#(scheme_0.pdcm_period * 1us);
			
			#(abort_delay * 1us);			
			disable_dsi_channels(2'b11);
			#(abort_duration * 1us);
			enable_dsi_channels(2'b11);
			#(scheme_0.pdcm_period * 1us);
			
			transaction_recorder.expect_tr_count_for_all_channels(2);

			`spi_frame_begin
				`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#50us;		
			`spi_frame_begin
			`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#50us
			`spi_frame_begin
			`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#100us;
		end	
	endtask
endclass