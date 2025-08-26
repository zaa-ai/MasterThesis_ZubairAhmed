class dsi3_clear_data_buffer_seq extends base_dsi_master_seq;

	`uvm_object_utils(dsi3_clear_data_buffer_seq)

	function new(string name = "");
		super.new("dsi3_clear_data_buffer");
	endfunction

	virtual task run_tests();
		log_sim_description("Testcase for clearing DSI data buffer", LOG_LEVEL_TOP);
		
		`create_and_send(clear_crm_data_buffer_seq)
		`create_and_send(clear_pdcm_data_buffer_seq)
		`create_and_send(clear_buffer_during_crm_seq)
		`create_and_send(clear_buffer_during_pdcm_seq)
		`create_and_send(clear_buffer_and_read_in_one_frame_seq)
		`create_and_send(clear_crm_and_pdcm_data_buffer_seq)
		`create_and_send(clear_single_channel_buffer_during_pdcm_seq)
		`create_and_send(clear_full_pdcm_buffer_seq)
		`create_and_send(clear_pdcm_data_with_tdma_scheme_upload_seq)
		`create_and_send(clear_pdcm_data_with_upload_tdma_packet_seq)
		`create_and_send(clear_buffer_during_pdcm_fine_delayed_seq)
	endtask
endclass
