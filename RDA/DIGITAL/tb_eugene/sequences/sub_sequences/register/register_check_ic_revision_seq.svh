class register_check_ic_revision_seq extends base_dsi_master_seq;

	`uvm_object_utils(register_check_ic_revision_seq)

	function new(string name = "");
		super.new("register_check_ic_revision");
	endfunction

	virtual task run_tests();
		log_sim_description("Check IC_REVISION register", LOG_LEVEL_SEQUENCE);
		check_ic_revision();
	endtask
endclass