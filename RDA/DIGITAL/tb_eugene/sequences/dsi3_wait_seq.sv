class dsi3_wait_seq extends base_dsi_master_seq;

	`uvm_object_utils(dsi3_wait_seq)

	function new(string name = "");
		super.new("dsi3_wait");
	endfunction
	
	virtual task run_tests();
		transaction_recorder.enable_recorder();
		log_sim_description("Testcase for DSI wait command", LOG_LEVEL_TOP);
		// disable TX Shift
		regmodel.DSI_common.common_DSI3_block_registers.DSI_TX_SHIFT.write(status, 0);
		
		`create_and_send(wait_on_each_channel_seq)
		`create_and_send(chained_wait_on_each_channel_seq)
		`create_and_send(check_wait_register_seq)
		`create_and_send(wait_maximum_on_all_channel_seq)
	endtask
endclass
