class syncb_short_pin_activation_seq extends dsi3_sync_base_seq;
	
	`uvm_object_utils(syncb_short_pin_activation_seq) 
	
	function new(string name = "");
		super.new("syncb_short_pin_activation");
	endfunction
	
	virtual task run_tests();
		tdma_scheme_pdcm scheme = new();
		
		log_sim_description("SYNCB with very short pin activation times", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		if(!scheme.randomize() with {packets.size() == 1; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US; symbol_count_min==8; symbol_count_max==8;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		for (int channel = 0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			set_tdma_scheme_pdcm(channel, scheme);
		end
		
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)
		
		
		for (int pulse_width = 1; pulse_width < 100; pulse_width += 10) begin
			transaction_recorder.clear_all();
			set_syncb(1'b0);
			#200us;
			
			`spi_frame_begin
				`spi_frame_create(spi_sync_dsi_channels_seq, external_sync == 1'b1; channel_bits == 2'b11;)
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 8'd1;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#200us;
			
			set_syncb(1'b1);
			#(pulse_width * 1ns);
			set_syncb(1'b0);
			#500us;
		
			if(pulse_width > 60) begin
				transaction_recorder.expect_tr_count_for_all_channels(1);
			end
			
			`spi_frame_begin
				`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11; )
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end		
			#100us;
		end
		
		transaction_recorder.disable_recorder();
		#500us;
	endtask
endclass