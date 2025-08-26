class dsi3_pdcm_seq extends base_dsi_master_seq;

	`uvm_object_utils(dsi3_pdcm_seq)

	function new(string name = "");
		super.new("dsi3_pdcm");
	endfunction
	
	virtual task run_tests();
		get_checker_config().enable_check_pdcm_period = 1'b1;

		log_sim_description("testcase for PDCM - periodic data collection mode", LOG_LEVEL_TOP);
		
		`create_and_send(start_pdcm_without_valid_tdma_scheme_seq)
        `create_and_send_with(single_pdcm_on_all_channels_seq, all_channels_correct == 1'b1;)
		`create_and_send(single_pdcm_on_single_channel_seq)
		`create_and_send_with(pdcm_random_denso_scheme_on_all_channels_seq, pulse_count == 1;)
		`create_and_send_with(pdcm_random_denso_scheme_on_all_channels_seq, pulse_count == 5;)
		`create_and_send_with(pdcm_random_denso_15_scheme_on_all_channels_seq, pulse_count == 3;)
		`create_and_send(pdcm_denso_scheme_all_source_ids_seq)
		
		`create_and_send(random_pdcm_and_different_bit_chip_times_seq);
		`create_and_send(pdcm_denso_15_single_missing_packet_seq);
		`create_and_send(pdcm_read_all_packets_missing_seq)
		
		repeat(10) begin
			log_sim_description($sformatf("PDCM with multiple random missing packets all channels"), LOG_LEVEL_SEQUENCE);
			`create_and_send(pdcm_denso_15_random_missing_packets_seq);
		end
		repeat(10) begin
			log_sim_description($sformatf("Read empty PDCM data with random TDMA schemes on random channels"), LOG_LEVEL_SEQUENCE);
			`create_and_send(pdcm_read_empty_data_seq);
		end
	
		log_sim_description("random PDCM with all possible source IDs", LOG_LEVEL_SEQUENCE);
		`create_and_send_with(random_pdcm_and_read_data_seq, active_channels > 0; source_id == dsi3_pkg::SID_0Bit;)
		`create_and_send_with(random_pdcm_and_read_data_seq, active_channels > 0; source_id == dsi3_pkg::SID_4Bit;)
		`create_and_send_with(random_pdcm_and_read_data_seq, active_channels > 0; source_id == dsi3_pkg::SID_8Bit;)
		`create_and_send_with(random_pdcm_and_read_data_seq, active_channels > 0; source_id == dsi3_pkg::SID_16Bit_CRC;)
		
		`create_and_send(pdcm_packet_count_error_seq)
		`create_and_send(pdcm_maximum_packet_count_error_seq)	
		`create_and_send(pdcm_read_without_pdcm_scheme_seq)
		`create_and_send(pdcm_read_without_pdcm_on_one_channel_scheme_seq)
		`create_and_send(upload_tdma_scheme_and_start_pdcm_in_one_frame_seq)
		`create_and_send(pdcm_early_single_packet_seq)
		`create_and_send(pdcm_late_single_packet_seq)
		`create_and_send(pdcm_symbol_count_error_seq)
		`create_and_send(pdcm_symbol_coding_error_seq)
		`create_and_send(pdcm_voltage_error_seq)
		`create_and_send(pdcm_voltage_error_before_slave_answer_seq)
		`create_and_send(pdcm_clock_ref_error_seq)
		`create_and_send(pdcm_clock_ref_error_during_pdcm_pulse_transmission_seq)
		`create_and_send(pdcm_receive_packet_with_more_than_255_symbols_seq)
		`create_and_send(pdcm_with_maximum_pulse_count_seq)
		`create_and_send(pdcm_min_max_periods_seq)
		`create_and_send(pdcm_packet_start_before_t__PDCM_START__seq)
		`create_and_send(pdcm_packets_too_late_seq)
		`create_and_send(pdcm_symbol_noise_on_all_channels_seq)
		`create_and_send(pdcm_chip_noise_on_all_channels_seq)
		`create_and_send(pdcm_single_packet_split_by_end_of_period_seq)
		`create_and_send(pdcm_short_inter_packet_gaps_seq)
		`create_and_send(pdcm_long_packets_end_at_receive_timeout_seq)
		`create_and_send(pdcm_denso_one_missing_and_one_too_large_packet_seq)
		`create_and_send(pdcm_denso_one_moving_packet_seq)
		
		`create_and_send(pdcm_ram_burst_read_seq)
		`create_and_send(pdcm_fill_buffer_seq)
		
		`create_and_send(random_pdcm_fill_data_buffer_seq);
		#1ms;
		
		log_sim_description("random PDCM with different periods, packet counts, source IDs, ...", LOG_LEVEL_SEQUENCE);
		repeat(10) begin
			`create_and_send(random_pdcm_and_read_data_seq)
			`create_and_send(random_pdcm_and_read_multiple_packets_seq)
			`create_and_send(pdcm_read_empty_data_seq)
		end
	endtask
endclass
