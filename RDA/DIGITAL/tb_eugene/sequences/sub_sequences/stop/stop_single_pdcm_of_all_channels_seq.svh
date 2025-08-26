class stop_single_pdcm_of_all_channels_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(stop_single_pdcm_of_all_channels_seq) 
    
	function new(string name = "");
		super.new("stop_single_pdcm_of_all_channels");
	endfunction

	virtual task run_tests();
		tdma_scheme_pdcm_denso scheme = new();
		
		log_sim_description("stop single PDCM when all channels do PDCM", LOG_LEVEL_SEQUENCE);
		
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)	
		set_tdma_scheme_pdcm(0, scheme);
		set_tdma_scheme_pdcm(1, scheme);
		
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			log_sim_description($sformatf("stop PDCM on channel %1d when all channels do PDCM", channel), LOG_LEVEL_OTHERS);
			transaction_recorder.enable_recorder();
			
			`spi_frame_begin
				`spi_frame_create(spi_sync_dsi_channels_seq, channel_bits == 2'b11; external_sync == 1'b0;)
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 5;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			#100us;
			`spi_frame_begin
				`spi_frame_create(spi_clear_dsi_command_queue_seq, channel_bits == 2'(1<<channel); )
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			#(scheme.pdcm_period * 1us);
			`spi_frame_begin
				`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			repeat(4) begin
				#(scheme.pdcm_period * 1us);
				`spi_frame_begin
					`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
			end
			
			// check pulses
			for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
				if (channel == i) begin
					transaction_recorder.expect_tr_count(i, 1);
				end 
				else begin
					transaction_recorder.expect_tr_count(i, 5);
				end
			end
			#0.5ms;
		end
		#100us;
	endtask
endclass

