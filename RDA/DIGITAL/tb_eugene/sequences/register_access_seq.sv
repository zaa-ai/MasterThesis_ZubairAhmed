class register_access_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(register_access_seq)

	function new(string name = "");
		super.new("register_access");
	endfunction : new
	
	virtual task run_tests();
		log_sim_description("Testcase for master register access", LOG_LEVEL_TOP);

		`create_and_send(register_check_ic_revision_seq)
		`create_and_send(register_read_tb_cnt_register_seq)
		`create_and_send(register_check_ring_buffers_seq)
		`create_and_send(register_miso_crc_example_seq)
		`create_and_send(register_irq_en_enable_all_irqs_seq)
		`create_and_send(register_dsi_irq_en_frontdoor_access_seq)
		`create_and_send(register_multiple_writes_in_one_frame_seq)
		`create_and_send(register_multiple_writes_with_tx_crc_in_one_frame_seq)
		`create_and_send(register_multiple_writes_with_tx_crc_in_one_wrong_crc_frame_seq)
		`create_and_send(register_write_to_invalid_addresses_seq)
		`create_and_send(register_spi_burst_read_zero_address_seq)
		`create_and_send(register_spi_burst_read_to_improve_coverage_seq)
		`create_and_send(register_jtag_burst_read_to_improve_coverage_seq)
		`create_and_send(register_read_ic_revision_during_startup_seq)
	endtask
endclass
