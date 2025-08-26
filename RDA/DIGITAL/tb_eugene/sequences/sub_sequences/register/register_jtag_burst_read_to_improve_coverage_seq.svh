class register_jtag_burst_read_to_improve_coverage_seq extends base_dsi_master_seq;

	`uvm_object_utils(register_jtag_burst_read_to_improve_coverage_seq)
	
	function new(string name = "");
		super.new("register_jtag_burst_read_to_improve_coverage");
	endfunction : new
	
	virtual task run_tests();
		jtag_read_elip_seq elip_read_seq;
		
		log_sim_description("JTAG read higher areas of address space", LOG_LEVEL_SEQUENCE);
		
		jtag_enable_with_tdo(1'b1);
		
		repeat(200) begin
			`uvm_do_on_with(elip_read_seq, m_jtag_master_agent.m_sequencer, {address inside {['h400:'hFFFF]}; init == 1;})			
			#1us;
		end
		
		jtag_disable();
	endtask
endclass