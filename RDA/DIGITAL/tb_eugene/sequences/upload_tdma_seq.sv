class upload_tdma_seq extends base_dsi_master_seq;

	`uvm_object_utils(upload_tdma_seq)

	function new(string name = "");
		super.new("upload_tdma");
	endfunction
	
	virtual task run_tests();

		log_sim_description("testcase for TDMA scheme uploads", LOG_LEVEL_TOP);
		
		`create_and_send(upload_random_valid_tdma_schemes_seq)
		`create_and_send(upload_random_invalid_tdma_schemes_seq)

	endtask
endclass
