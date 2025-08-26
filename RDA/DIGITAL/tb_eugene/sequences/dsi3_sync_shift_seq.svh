class dsi3_sync_shift_seq extends base_dsi_master_seq;

	`uvm_object_utils(dsi3_sync_shift_seq)

	function new(string name = "");
		super.new("dsi3_sync_shift");
	endfunction
	
	virtual task run_tests();
		log_sim_description("Basic testcase for PDCM syncing and shifting", LOG_LEVEL_TOP);
		
		`create_and_send(pdcm_shift_sync_with_register_writes_seq)
		`create_and_send(pdcm_shift_sync_channel_1_before_0_seq)
		`create_and_send(pdcm_shift_sync_change_during_pdcm_seq)
		`create_and_send_with(pdcm_sync_change_while_pdcm_seq, initial_pdcm_sync == 1'b1;)
		`create_and_send_with(pdcm_sync_change_while_pdcm_seq, initial_pdcm_sync == 1'b0;)
		`create_and_send(pdcm_sync_seq)
		`create_and_send(crm_shift_seq)
		`create_and_send(discovery_mode_shift_seq)
		`create_and_send_with(pdcm_shift_seq, sync_pdcm == 1'b0;)
		`create_and_send_with(pdcm_shift_seq, sync_pdcm == 1'b1;)
		`create_and_send(apply_shift_while_in_pdcm_seq)
		`create_and_send(mix_starts_of_crm_seq)
		`create_and_send(sync_between_pdcm_and_crm_seq)
		`create_and_send(pdcm_sync_with_different_tdma_schemes_seq)
	endtask
endclass
