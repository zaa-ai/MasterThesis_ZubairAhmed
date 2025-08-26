`include "svunit_defines.svh"

module test;
	
	`include "uvm_macros.svh"
	import svunit_pkg::svunit_testcase;
	import svunit_uvm_mock_pkg::*;
	import project_pkg::*;
	import uvm_pkg::*;
	import dsi3_pkg::*;
	import common_test_pkg::*;
	import unit_test_pkg::*;

	string name = "tdma_buffer_test";
	svunit_testcase svunit_ut;
	
	//===================================
	// This is the UUT that we're 
	// running the Unit Tests on
	//===================================
	`clk_def(50ns)
	
	`tick_gen
	
	top_config				_top_config;
	tdma_sequencer			sequencer;
	tdma_seq				seq;
	
	/*###   interface definitions   ######################################################*/
	elip_full_if elip ();
	tdma_interface tdma ();
	
	elip_bus_if elip_bus ();
	
	
	/*###   instance   ###################################################################*/
	tdma_buffer #(.BASE_ADDRESS(16'h100)) i_tdma_buffer (
		.clk_rst(clk_rst.slave ),
		.elip   (elip.master   ),
		.tdma   (tdma.slave    )
	);
	
	interface_converter_elip_full_2_elip_bus i_interface_converter (
		.clk_rst    (clk_rst.slave             ),
		.elip_full  (elip.slave	               ), 
		.elip_bus   (elip_bus                  ));
	
	// no reset of RAM!
	clk_reset_if clk_rst_ram ();
	assign	clk_rst_ram.clk = clk_rst.clk;
	initial begin
		clk_rst_ram.rstn = 1'b1;
		#10;
		clk_rst_ram.rstn = 1'b0;
		#10;
		clk_rst_ram.rstn = 1'b1;
	end
	
	ram_model #(
		.OFFSET('h0100),
		.RAM_SIZE  ('h40)
	) i_command_buffer_model (
		.clk_rst   (clk_rst_ram.slave  ), 
		.elip      (elip.slave     )
	);
	
	/*###   start simulation   ######################################################*/
	initial begin
		_top_config = new("_top_config");
		
		uvm_config_db #(top_config)::set(null, "uvm_test_top", "_top_config", _top_config);
		uvm_config_db #(top_config)::set(null, "uvm_test_top.m_env", "_top_config", _top_config);
		
		_top_config._elip_config.vif = elip_bus;
		_top_config._tdma_config.vif = tdma;
		
		run_test();
	end
	
	//===================================
	// Build
	//===================================
	function void build();
		svunit_ut = new(name);
	endfunction

	//===================================
	// Setup for running the Unit Tests
	//===================================
	task setup();
		svunit_ut.setup();
		#100ns;
		set_por();
		#100ns;
		enable_clk = 1'b1;
		_top_config._check_elip.base_address = 'h0100;
		_top_config._check_elip.size		 = 'h0040;
	endtask

	//===================================
	// Here we deconstruct anything we 
	// need after running the Unit Tests
	//===================================
	task teardown();
		enable_clk = 1'b0;
		svunit_ut.teardown();
	endtask
	
	//===================================
	// All tests are defined between the
	// SVUNIT_TESTS_BEGIN/END macros
	//
	// Each individual test must be
	// defined between `SVTEST(_NAME_)
	// `SVTEST_END
	//
	// i.e.
	//	 `SVTEST(mytest)
	//		 <test code>
	//	 `SVTEST_END
	//===================================
	
	task _wait(int clocks);
		wait_for_n_clocks(clocks);
	endtask
	
	task start_seq();
		_top_config._check_elip.write_tdma(seq);
		seq.start(sequencer);
	endtask
	
	task check_for_errors();
		automatic int errors;
		errors = _top_config._check_elip.get_error_count();
		if(!uvm_report_mock::verify_complete())
			errors++;
		`FAIL_UNLESS_EQUAL(errors, 0)
	endtask
	
	`SVUNIT_TESTS_BEGIN
	begin
		#1;
		sequencer = _top_config._tdma_agent.m_sequencer;
		write_packet();
		write_header();
		read_packet();
		read_header();
		random_tests();
	end	 
	`SVUNIT_TESTS_END
	
	task automatic write_packet();
		`SVTEST("write packet")
			seq = tdma_packet_seq::create_seq();
			seq.write = 1'b1;
			start_seq();
			check_for_errors();
		`SVTEST_END
	endtask
	
	task automatic write_header();
		`SVTEST("write packet")
			seq = tdma_header_seq::create_seq();
			seq.write = 1'b1;
			start_seq();
			check_for_errors();
		`SVTEST_END
	endtask
	
	task automatic read_packet();
		`SVTEST("read packet")
			seq = tdma_packet_seq::create_seq();
			seq.write = 1'b0;
			start_seq();
			check_for_errors();
		`SVTEST_END
	endtask
	
	task automatic read_header();
		`SVTEST("read packet")
			seq = tdma_header_seq::create_seq();
			seq.write = 1'b0;
			start_seq();
			check_for_errors();
		`SVTEST_END
	endtask
	
	task automatic random_tests();
		for (int loop = 0; loop < 1000; loop++) begin
			`SVTEST($sformatf("random tests [%3d]", loop))
				randcase
					1 : seq = tdma_header_seq::create_seq();
					10: seq = tdma_packet_seq::create_seq();
				endcase
				start_seq();
				check_for_errors();
			`SVTEST_END
		end
	endtask
	
endmodule
