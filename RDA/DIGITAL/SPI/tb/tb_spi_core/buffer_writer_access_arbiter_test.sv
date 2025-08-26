/**
 * Module: buffer_writer_access_arbiter_test
 * 
 * TODO: Add module documentation
 */
module buffer_writer_access_arbiter_test import project_pkg::*; ();
	
	import svunit_pkg::svunit_testcase;
	
	svunit_testcase svunit_ut;
	string name = "buffer_writer_access_arbiter_test";
	
	logic	get_access_fsm, get_access_clearing;
	logic	grant_access_fsm, grant_access_clearing;
	
	`clk_def(27777ps)

	//===================================
	// This is the UUT that we're
	// running the Unit Tests on
	//===================================
	buffer_writer_access_arbiter i_buffer_writer_access_arbiter (
			.clk_rst                  (clk_rst                 ), 
			.i_get_access_fsm         (get_access_fsm        ), 
			.i_get_access_clearing    (get_access_clearing   ), 
			.o_grant_access_fsm       (grant_access_fsm      ), 
			.o_grant_access_clearing  (grant_access_clearing ));
	
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
		/* Place Setup Code Here */
		get_access_clearing = 1'b0;
		get_access_fsm = 1'b0;;
		wait_for_n_clocks(10);
	endtask

	//===================================
	// Here we deconstruct anything we
	// need after running the Unit Tests
	//===================================
	task teardown();
		svunit_ut.teardown();
		/* Place Teardown Code Here */
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


	`SVUNIT_TESTS_BEGIN
		enable_clk = 1'b1;
		
		`SVTEST("reset")
			`FAIL_UNLESS_EQUAL(grant_access_fsm, 1'b0)
			`FAIL_UNLESS_EQUAL(grant_access_clearing, 1'b0)
		`SVTEST_END
			
		`SVTEST("grant access FSM")
			get_access_fsm = 1'b1;
			wait_for_n_clocks(1);
			`FAIL_UNLESS_EQUAL(grant_access_fsm, 1'b1)
			`FAIL_UNLESS_EQUAL(grant_access_clearing, 1'b0)
			get_access_fsm = 1'b0;
			wait_for_n_clocks(1);
			`FAIL_UNLESS_EQUAL(grant_access_fsm, 1'b0)
			`FAIL_UNLESS_EQUAL(grant_access_clearing, 1'b0)
		`SVTEST_END
		
		`SVTEST("grant access 'clearing'")
			get_access_clearing = 1'b1;
			wait_for_n_clocks(1);
			`FAIL_UNLESS_EQUAL(grant_access_fsm, 1'b0)
			`FAIL_UNLESS_EQUAL(grant_access_clearing, 1'b1)
			get_access_clearing = 1'b0;
			wait_for_n_clocks(1);
			`FAIL_UNLESS_EQUAL(grant_access_fsm, 1'b0)
			`FAIL_UNLESS_EQUAL(grant_access_clearing, 1'b0)
		`SVTEST_END
		
		`SVTEST("check priority grant access 'clearing'")
			get_access_clearing = 1'b1;
			get_access_fsm = 1'b1;
			wait_for_n_clocks(1);
			`FAIL_UNLESS_EQUAL(grant_access_fsm, 1'b0)
			`FAIL_UNLESS_EQUAL(grant_access_clearing, 1'b1)
		`SVTEST_END
		
		`SVTEST("check priority grant access 'FSM' when active")
			get_access_fsm = 1'b1;
			wait_for_n_clocks(1);
			`FAIL_UNLESS_EQUAL(grant_access_fsm, 1'b1)
			`FAIL_UNLESS_EQUAL(grant_access_clearing, 1'b0)
			get_access_clearing = 1'b1;
			wait_for_n_clocks(2);
			`FAIL_UNLESS_EQUAL(grant_access_clearing, 1'b0)
			`FAIL_UNLESS_EQUAL(grant_access_fsm, 1'b1)
			get_access_fsm = 1'b0;
			wait_for_n_clocks(1);
			`FAIL_UNLESS_EQUAL(grant_access_fsm, 1'b0)
			`FAIL_UNLESS_EQUAL(grant_access_clearing, 1'b1)
		`SVTEST_END
		
		enable_clk = 1'b0;
	`SVUNIT_TESTS_END

endmodule
