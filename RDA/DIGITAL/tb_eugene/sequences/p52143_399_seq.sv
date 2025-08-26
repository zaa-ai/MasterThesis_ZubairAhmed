class p52143_399_seq extends base_dsi_master_seq;

	`uvm_object_utils(p52143_399_seq)

	function new(string name = "");
		super.new("p52143_399");
	endfunction

	virtual task run_tests();
		log_sim_description("Testcase for Jira Issue P52143-399", LOG_LEVEL_TOP);
		
		repeat(15) begin
			`create_and_send_with(random_pdcm_seq, channels == 2'b11; symbol_count inside {[150:160]}; pulse_count inside {[10:15]}; chip_time==3;)
			#1ms;
		end
	endtask
endclass

