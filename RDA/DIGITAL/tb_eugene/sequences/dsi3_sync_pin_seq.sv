class dsi3_sync_pin_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(dsi3_sync_pin_seq)
	
	function new(string name = "");
		super.new("dsi3_sync_pin");
	endfunction
	
	virtual task run_tests();
		log_sim_description("Testcase for DSI3 synchronize channels using SYNCB pin", LOG_LEVEL_TOP);
		
		`create_and_send(measure_t_dsi3_sync_seq)
		`create_and_send(external_sync_crm_seq)
		`create_and_send(external_sync_pdcm_seq)
		`create_and_send(syncb_only_some_channels_seq)
		`create_and_send(mixed_external_internal_sync_seq)
		`create_and_send(syncb_already_active_seq)
		`create_and_send(syncb_during_running_crm_seq)
		`create_and_send(syncb_sync_error_seq)
		`create_and_send(syncb_random_commands_seq)
		`create_and_send(external_sync_crm_short_pulse_seq)
		`create_and_send(sync_master_crm_seq)
		`create_and_send(syncb_short_pin_activation_seq)
        
		#100us;
	endtask
endclass
