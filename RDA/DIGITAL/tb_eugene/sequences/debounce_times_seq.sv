
class debounce_times_seq extends base_dsi_master_seq;

	`uvm_object_utils(debounce_times_seq)

	function new(string name = "");
		super.new("debounce_times");
	endfunction

	virtual task run_tests();
		// disable automatic check for HE flag
		get_checker_config().enable_hardware_error_check = 1'b0;
		get_checker_config().enable_master_transmission_checker = 1'b0;
		
		log_sim_description("Testcase for measuring different debounce times", LOG_LEVEL_TOP);
		
		`create_and_send_with(resb_debounce_measure_seq, 		start_time == 1ns; end_time == 3us;  	step_time == 50ns;	wait_time_out == 100us;)
		`create_and_send_with(vccuv_debounce_measure_seq, 		start_time == 1ns; end_time == 200us; 	step_time == 5us;	wait_time_out == 200us;)
		`create_and_send_with(ref_fail_debounce_measure_seq, 	start_time == 1ns; end_time == 200us; 	step_time == 1us;	wait_time_out == 200us;)
		`create_and_send_with(ldo_uv_debounce_measure_seq,	 	start_time == 1ns; end_time == 100us; 	step_time == 1us;	wait_time_out == 200us;)		
		`create_and_send_with(ot_debounce_measure_seq,		 	start_time == 1ns; end_time == 100us; 	step_time == 1us;	wait_time_out == 200us;)
		reset();
		
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			`create_and_send_with(dsi_uv_debounce_measure_seq, 		channel == local::channel; start_time == 1ns; end_time == 10us; step_time == 50ns; wait_time_out == 1ms;)
		end
		
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			`create_and_send_with(dsi_mon_to_debounce_measure_seq, 	channel == local::channel; start_time == 1ns; end_time == 7ms;  step_time == 500us; wait_time_out == 7ms;)
			reset();
		end
	endtask
	
endclass
