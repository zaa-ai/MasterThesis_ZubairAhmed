
class dsi3_crm_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(dsi3_crm_seq)

	function new(string name = "");
		super.new("dsi3_crm");
	endfunction

	virtual task run_tests();
		log_sim_description("Basic testcase for command response mode", LOG_LEVEL_TOP);

		`create_and_send(crm_single_channel_transmit_seq)
		
		log_sim_description("single CRM transmit on all channels", LOG_LEVEL_SEQUENCE);
		`create_and_send_with(single_crm_on_all_channels_seq, { all_channels_correct == 1'b1;})
		
		`create_and_send(single_crm_on_each_channel_seq)
		`create_and_send(crm_command_without_data_seq)
		`create_and_send(crm_broadcast_and_read_seq)
		`create_and_send(crm_read_empty_data_seq)
		`create_and_send(crm_with_ffff_data_seq)
		`create_and_send(crm_many_on_one_channel_one_on_all_channels_seq) 
		`create_and_send(crm_read_data_using_multiple_tx_crc_seq)
		`create_and_send(crm_without_slave_answer_seq)
		`create_and_send(crm_transmit_and_read_in_one_frame_seq)
		`create_and_send(crm_many_crm_in_one_spi_frame_started_with_tx_crc_seq)
		`create_and_send(crm_wrong_symbol_counts_seq)
		`create_and_send(crm_CRM_TIME_lower_than_transmission_time_seq)
		`create_and_send(crm_CRM_TIME_NR_lower_than_transmission_time_seq)
		`create_and_send(crm_maximum_CRM_TIME_seq)
		`create_and_send(crm_maximum_CRM_TIME_NR_seq)
		`create_and_send(crm_maximum_CRM_TIME_with_multiple_answers_seq)
		`create_and_send(crm_CRM_TIME_change_during_crm_transmission_seq)
		`create_and_send(crm_late_long_slave_answers_seq)
		`create_and_send(crm_late_short_slave_answers_seq)
		`create_and_send(crm_very_long_slave_answers_seq)
		`create_and_send(crm_very_long_slave_answers_with_additional_crm_seq)
		`create_and_send(crm_two_short_slave_answers_seq)
		`create_and_send(crm_clock_ref_error_during_crm_transmission_seq)
		`create_and_send(crm_clock_ref_error_in_crm_for_all_channels_seq)
		`create_and_send(crm_clock_ref_inside_crm_transmission_seq)
		`create_and_send(crm_clock_ref_disable_during_crm_transmission_seq)
		`create_and_send(crm_clock_ref_error_during_crm_transmission_without_slave_answer_seq)
		`create_and_send(crm_disable_clock_ref_during_transmission_p52143_697_seq)
		`create_and_send(crm_voltage_error_in_crm_for_all_channels_seq)
		`create_and_send(crm_symbol_coding_error_in_crm_for_all_channels_seq)
		`create_and_send(crm_chip_coding_error_in_crm_for_all_channels_seq)
		`create_and_send(crm_crc_en_seq)
		`create_and_send(crm_multiple_crms_in_one_command_frame_seq)
		`create_and_send(crm_multiple_broadcast_crms_in_one_command_frame_seq)
		`create_and_send(crm_symbol_noise_on_all_channels_seq)
		`create_and_send(crm_dsi_fast_config_access_seq)
		`create_and_send(crm_check_different_chiptimes_and_bittimes_seq)
		`create_and_send(crm_fill_buffer_seq)
		`create_and_send(crm_random_on_different_channels_seq)
		`create_and_send(crm_read_status_during_reception_seq)
		#1ms;
	endtask
endclass
