class dsi3_discovery_mode_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(dsi3_discovery_mode_seq)

	function new(string name = "");
		super.new("dsi3_discovery_mode");
	endfunction
	
	// TODO: modify timing (early/late slaves)

	virtual task run_tests();
		dsi3_pkg::dsi3_bit_time_e bit_time;
		
		log_sim_description("Testcase for discovery mode", LOG_LEVEL_TOP);
		checker_config::get().enable_measure_discovery_pulse = 1'b1;
		
		`create_and_send_with(dsi3_discovery_mode_overflow_seq, channels == 2'b11;)
		`create_and_send(dsi3_discovery_mode_without_slaves_seq)
		
		for (bit_time=dsi3_pkg::BITTIME_8US; bit_time < dsi3_pkg::BITTIME_UNUSED; bit_time = bit_time.next()) begin
			log_sim_description($sformatf("discovery mode with 0 to 15 slaves and %s bit time", bit_time.name()), LOG_LEVEL_SEQUENCE);
			for (int i = 0; i <= 15; i++) begin
				`create_and_send_with(dsi3_random_discovery_mode_seq, channels == 2'b11; number_of_slaves == i; bit_time == local::bit_time;)
			end
		end
		
		// do some random discovery mode
		log_sim_description($sformatf("random discovery mode with different slave count and bit time"), LOG_LEVEL_SEQUENCE);
		repeat(20) begin
			`create_and_send(dsi3_random_discovery_mode_seq)
		end
		#1ms;
	endtask
endclass
