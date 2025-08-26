class register_read_ic_revision_during_startup_seq extends base_dsi_master_seq;

	`uvm_object_utils(register_read_ic_revision_during_startup_seq)
	
	function new(string name = "");
		super.new("register_read_ic_revision_during_startup");
	endfunction
	
	virtual task run_tests();
		log_sim_description("Read IC_REVISION during startup", LOG_LEVEL_SEQUENCE);
		get_checker_config().enable_hardware_error_check = 1'b0;
		
		set_resb(0);
		#100us;
		set_resb(1); 
		#100us;
		
		while(get_rfc() == 1'b0) begin
			check_ic_revision();
		end
		check_rfc(1'b1);
		check_ic_revision();
	endtask
endclass