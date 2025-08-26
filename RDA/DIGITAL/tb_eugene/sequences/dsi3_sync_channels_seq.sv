class dsi3_sync_channels_seq extends base_dsi_master_seq;

	`uvm_object_utils(dsi3_sync_channels_seq)

	function new(string name = "");
		super.new("dsi3_sync_channels");
	endfunction

	// TODO: ECC Fehler pro Channel -> SYNC_ERR
	
	virtual task run_tests();
		transaction_recorder.enable_recorder();
		
		log_sim_description("Testcase for DSI3 synchronize channels command", LOG_LEVEL_TOP);
		
		`create_and_send(check_sync_reg_for_crm_seq)
		`create_and_send(check_sync_reg_for_pdcm_seq)
		`create_and_send(check_sync_reg_for_channel_pairs_seq)
		`create_and_send(first_sync_at_all_channels_then_single_crms_seq)
		`create_and_send(sync_multiple_crm_in_one_frame_seq)
		`create_and_send(sync_multiple_crm_in_different_frames_seq)
		`create_and_send(double_sync_crm_in_different_frames_seq)
		`create_and_send(sync_multiple_crm_per_channel_in_different_frames_seq)
		`create_and_send(wait_for_sync_flag_seq)
		`create_and_send(shut_off_during_sync_seq)
		`create_and_send(shut_off_before_sync_seq)
		`create_and_send(clear_queue_during_sync_seq)
		`create_and_send(clear_queue_of_all_channels_during_sync_seq)
		
		`create_and_send(sync_pdcm_at_all_channels_seq)
		`create_and_send(sync_crm_seq)
		`create_and_send(sync_pdcm_seq)
		`create_and_send(sync_random_commands_seq)
		#100us;
	endtask
endclass
