class pdcm_measure_t__PDCM_END__seq extends base_dsi_master_seq;
	
	`uvm_object_utils(pdcm_measure_t__PDCM_END__seq)

	function new(string name = "");
		super.new("pdcm_measure_t__PDCM_END__");
	endfunction
	
	task run_tests();
		tdma_scheme_pdcm scheme = new();
		chip_times_iterator_with_register_model chip_iterator = new(regmodel);

		log_sim_description($sformatf("measure t__PDCM,END__ for all chip times"), LOG_LEVEL_SEQUENCE);
		checker_config::get().enable_measure_pdcm_pulse = 1'b0;
		
		while(chip_iterator.has_next()) begin
			int chip_time = chip_iterator.get_current();
			int response_duration = chip_time * 8 * 3;
			int latest_start; 
			
			log_sim_description($sformatf("measure t__PDCM,END__ for chip time of %2dus", chip_time), LOG_LEVEL_OTHERS);
			
			if(!scheme.randomize() with {packets.size() == 1; symbol_count_min == 8; symbol_count_max == 8; chiptime == local::chip_time; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
			scheme.pdcm_period = 200;
			scheme.packets[0].set_start_time_window(30, 195);
			
			`upload_tdma_scheme_with(scheme, channels == 2'b01;)
			set_tdma_scheme_pdcm(0, scheme);
			
			chip_iterator.apply_next();
			
			latest_start = scheme.pdcm_period - edf_parameters.recommended.t__PDCM_END__.get_min_as_int() - response_duration;
			
			for(int response_start = latest_start - (6*chip_time); response_start < latest_start+10; response_start += 1) begin
				spi_read_pdcm_frame_seq read_1_seq, read_2_seq;
				
				scheme.packets[0].set_start_time_window(response_start, response_start);
				scheme.packets[0].tolerance_int = 1000;
				`spi_frame_begin
					`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b01; pulse_count == 2;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				
				#20us;
				#(2 * scheme.pdcm_period * 1us);
				// read data of all 2 PDCM frames in one SPI frame
				`spi_frame_begin
					`spi_frame_send(read_1_seq, channel_bits == 2'b01;)
					`spi_frame_send(read_2_seq, channel_bits == 2'b01;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				
				if(read_1_seq.get_data_packet(2'd0, 0).get_value(TE) == 1'b1 || read_2_seq.get_data_packet(2'd0, 0).get_value(TE) == 1'b1) begin
					log_sim_measure ("t__PDCM,END__", $sformatf("%0d", (scheme.pdcm_period - response_duration - response_start - (6*chip_time))), $sformatf("at chip time %2dus", chip_time));
					break;
				end
				#300us;
			end
			#300us;
		end
		registers.reset_register(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG);
		checker_config::get().enable_measure_pdcm_pulse = 1'b1;
	endtask
	
endclass
