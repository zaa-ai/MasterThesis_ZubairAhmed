class stop_finite_pdcm_at_random_time_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(stop_finite_pdcm_at_random_time_seq) 
	
	function new(string name = "");
		super.new("stop_finite_pdcm_at_random_time");
	endfunction

	/**
	 * Try to stop/clear a running finite (pulse count != 0) PDCM. 
	 */
	virtual task run_tests();
		tdma_scheme_pdcm scheme = new();
		
		log_sim_description("stop PDCM on all channels at random time", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();

		if(!scheme.randomize() with {packets.size() == 1; symbol_count_min == 4; symbol_count_max == 4; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)
		set_tdma_scheme_pdcm(0, scheme);
		set_tdma_scheme_pdcm(1, scheme);
				
		repeat(10) begin
			spi_pdcm_seq pdcm_seq;
			int delay;
			int delay_fine;
			
			`spi_frame_begin
				`spi_frame_send(pdcm_seq, channel_bits == 2'b11; pulse_count inside {[10:32]};)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#15us;
			
			for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
				registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_STAT.PULSECNT, pdcm_seq.pulse_count);
			end
			
			randcase
				1: delay = $urandom_range(100, 5_000);
				1: delay = 0;
			endcase
			delay_fine = $urandom_range(1, 999);
			#(delay * 1us + delay_fine * 1ns);
			
			`spi_frame_begin
				`spi_frame_create(spi_clear_dsi_command_queue_seq, channel_bits == 2'b11; )
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			#50us;
			transaction_recorder.clear_all();
			#(2* scheme.pdcm_period * 1us);	
			for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
				registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_STAT.PULSECNT, 0);
				transaction_recorder.expect_tr_count_for_all_channels(0);
			end
		end
		
		`spi_frame_begin
			`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; crm_buffer == 1'b1; pdcm_buffer == 1'b1;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		transaction_recorder.disable_recorder();
	endtask
endclass