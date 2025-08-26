class dsi3_iload_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(dsi3_iload_seq)

	function new(string name = "");
		super.new("dsi3_iload");
	endfunction

	virtual task run_tests();
		log_sim_description("Basic testcase for quiescent current commands", LOG_LEVEL_TOP);
		
		log_sim_description($sformatf("Quiescent current measurement on random channels with a random load"), LOG_LEVEL_SEQUENCE);
        repeat (20) begin
            for (int channels = 1; channels < 1<<project_pkg::DSI_CHANNELS; channels++) begin
                `create_and_send_with(quiescent_current_seq, channel_bits == local::channels[1:0];)
            end
        end
        
		log_sim_description($sformatf("Manual quiescent current measurement on random channels with a random load"), LOG_LEVEL_SEQUENCE);
        repeat (20) begin
            for (int channels = 1; channels < 1<<project_pkg::DSI_CHANNELS; channels++) begin
                `create_and_send_with(manual_quiescent_current_measurement_seq, channel_bits == local::channels[1:0];)
            end
        end
        
		#0.2ms;
    endtask
endclass
