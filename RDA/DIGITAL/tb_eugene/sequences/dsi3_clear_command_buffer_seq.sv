class dsi3_clear_command_buffer_seq extends base_dsi_master_seq;

	`uvm_object_utils(dsi3_clear_command_buffer_seq)

	function new(string name = "");
		super.new("dsi3_clear_command_buffer");
	endfunction

	/**
	 * Task: run_tests
	 */
	virtual task run_tests();
		log_sim_description("Testcase for clearing DSI command buffer", LOG_LEVEL_TOP);
		
		`create_and_send(stop_single_pdcm_of_all_channels_seq)
		`create_and_send(stop_queued_crm_commands_seq)
		`create_and_send(stop_wait_command_seq)
		`create_and_send(stop_finite_pdcm_at_random_time_seq)
		`create_and_send(stop_infinite_pdcm_at_random_time_seq)
		`create_and_send(stop_random_command_queue_seq)
		`create_and_send(stop_command_queue_within_command_frame_seq)
		`create_and_send(stop_crm_directly_after_start_seq)
	endtask
endclass
