
/*
 Created Verilog pattern using following command line:
  
	perl /heimat/dmos/all/mkue/workspace_17402/PE-52143/libraries/pl_ecps/ecps2verilog.pl 
		--merge-all-pattern E52143A_compare 
		--signal-configuration /heimat/dmos/all/mkue/workspace_17402/PE-52143/E52143A.signalconfig 
		--timing-configuration /heimat/dmos/all/mkue/workspace_17402/PE-52143/E52143A.timingconfig 
		--channel-mapping-name simulation 
		--output-path /heimat/dmos/all/mkue/workspace_17402/PE-52143/target/verilog 
		--pattern /heimat/dmos/all/mkue/workspace_17402/PE-52143/target/ecps/simulation.pattern
*/

class pattern_compare_seq extends base_dsi_master_seq;

	`uvm_object_utils(pattern_compare_seq)

	function new(string name = "");
		super.new("pattern_compare");
	endfunction

	virtual task run_tests();
		log_sim_description("Testcase for executing a register compare using Pattern-Explorer generated Verilog module", LOG_LEVEL_TOP);
		
		compare_ic_revision_pattern();
	endtask
	
	virtual task compare_ic_revision_pattern(); 
		E52143A_compare_wrapper	wrapper_class = get_wrapper();
		log_test("ECPS simulation to compare IC_REVISION register");
		
		// force IC_REVISION to expected value
		hdl_force("top_tb.th.i_dut_wrapper.xtop.xdigtop.i_logic_top.i_main_control.i_ic_revision.o_ic_revision", 16'd1500);
		
		jtag_enable_with_tdo(1'b1);
		#5us;
		
		enable_ecps_pattern();
		
		wrapper_class.execute(E52143A_compare_pkg::simulation_TM_COMPARE);
		wrapper_class.execute(E52143A_compare_pkg::simulation_TM_COMPARE);
		
		disable_ecps_pattern();
		#1ms;
	endtask
	
	function E52143A_compare_wrapper get_wrapper();
		E52143A_compare_wrapper	wrapper_class;
		if (!uvm_config_db#(E52143A_compare_wrapper)::get(m_sequencer, "", "pattern_wrapper", wrapper_class))
			`uvm_error(get_type_name(), "Unable to get pattern wrapper from config DB!")
		return wrapper_class;				
	endfunction
	
endclass
