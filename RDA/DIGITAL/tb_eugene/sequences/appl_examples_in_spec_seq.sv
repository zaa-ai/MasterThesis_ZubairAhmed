class appl_examples_in_spec_seq extends base_dsi_master_seq;

	`uvm_object_utils(appl_examples_in_spec_seq)

	function new(string name = "");
		super.new("appl_examples_in_spec");
	endfunction

	virtual task run_tests();

		log_sim_description("Simulate the application examples described in specification", LOG_LEVEL_TOP);
        
		`create_and_send_with(spec_Sync_CRM_on_DSI_seq, sync_set == unsynchronized;)
		`create_and_send_with(spec_Sync_CRM_on_DSI_seq, sync_set == synchronized;)
		`create_and_send_with(spec_Sync_CRM_on_DSI_seq, sync_set == wait_before_broadcast;)
		`create_and_send(spec_Sync_IDLE_DSI_seq)
		`create_and_send(spec_external_Sync_on_DSI_seq) 
        `create_and_send(spec_DSI_wait_seq)
		
		log_sim_description("CRM Command Sequence(Equal commands)", LOG_LEVEL_SEQUENCE);
        `create_and_send(spec_CRM_command_seq)
		
        `create_and_send(spec_CRM_configuration_seq)
 	    `create_and_send(spec_single_frame_pdcm_read_seq)
		`create_and_send(spec_multiple_frame_pdcm_read_seq) 
		`create_and_send(spec_multiple_frame_pdcm_lang_packet_read_seq) 
		`create_and_send(spec_measurement_command_stack_seq) 
	endtask
endclass

