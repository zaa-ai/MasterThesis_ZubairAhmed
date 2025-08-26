class spi_errors_seq extends base_dsi_master_seq;

	`uvm_object_utils(spi_errors_seq)

	function new(string name = "");
		super.new("spi_errors");
	endfunction

	virtual task run_tests();
		get_checker_config().enable_check_pdcm_period = 1'b1;
		log_sim_description("Testcase for different kinds of SPI errors", LOG_LEVEL_TOP);
		
		`create_and_send(spi_access_irq_en_wrong_crc_seq);
		`create_and_send(spi_access_irq_en_wrong_and_correct_tx_crc_seq)
		`create_and_send(spi_access_irq_en_correct_and_wrong_tx_crc_seq)
		`create_and_send(spi_start_frame_with_tx_crc_seq)
		`create_and_send(spi_bit_count_errors_seq)
		`create_and_send(spi_crc_ends_with_zeros_seq)
		`create_and_send(spi_single_command_ignored_seq)
		`create_and_send(spi_multiple_command_ignored_seq)
		
		`create_and_send(spi_frame_ends_with_reset_command_seq)
		`create_and_send(spi_frame_starts_with_reset_command_seq)
		`create_and_send(spi_multiple_reset_commands_seq)
		`create_and_send(spi_reset_random_command_frame_seq)
		`create_and_send(spi_reset_after_valid_command_frame_seq)
		`create_and_send(spi_reset_with_bit_count_errors_seq)
		`create_and_send(spi_reset_full_spi_command_buffer_seq)
		`create_and_send(spi_traffic_with_csb_high_seq)
		`create_and_send(spi_incomplete_register_reads_seq)
		`create_and_send(spi_incomplete_burst_register_reads_seq)
		`create_and_send(spi_incomplete_read_crm_data_seq)
		`create_and_send(spi_incomplete_read_crm_data_bit_count_seq)
		`create_and_send(spi_incomplete_read_pdcm_single_packet_seq)
		`create_and_send(spi_incomplete_read_pdcm_denso_15_seq)
		`create_and_send(spi_incomplete_read_pdcm_with_maximum_size_scheme_seq)
		`create_and_send(spi_incomplete_reset_command_seq)
		`create_and_send(spi_burst_read_with_wrong_tx_crc_seq)
		`create_and_send(spi_read_register_and_crm_transmit_with_crc_command_seq)
		`create_and_send(spi_hw_fail_during_spi_frame_seq)
		#100us;
	endtask
endclass
