`include "svunit_defines.svh"

module ecc_register_test import project_pkg::*; ();

	import svunit_pkg::svunit_testcase;
	import common_test_pkg::*;

	string name = "ecc_register_test";
	svunit_testcase svunit_ut;

	//===================================
	// This is the UUT that we're
	// running the Unit Tests on
	//===================================
	`clk_def(27777ps)

	`tick_gen

	/*###      ######################################################*/

	/*###   generic 16 bit ecc register instance   ##################*/
	logic	    waccess_16, raccess_16, ecc_fail_16;
	logic[15:0] wdata_16;
	logic[15:0] rdata_16;

	ecc_register #(
			.WIDTH (16),
			.RESET_VAL(0)
		) i_ecc_register_16 (
			.clk_rst                (clk_rst),
			.i_waccess              (waccess_16),
			.i_raccess              (raccess_16),
			.i_wdata                (wdata_16),
			.o_rdata                (rdata_16),
			.o_ecc_fail             (ecc_fail_16));

	/*###   generic 5 bit ecc register instance   ##################*/
	logic      waccess_5, raccess_5, ecc_fail_5;
	logic[4:0] wdata_5;
	logic[4:0] rdata_5;

	ecc_register #(
			.WIDTH (5),
			.RESET_VAL(0)
		) i_ecc_register_5 (
			.clk_rst                (clk_rst),
			.i_waccess              (waccess_5),
			.i_raccess              (raccess_5),
			.i_wdata                (wdata_5),
			.o_rdata                (rdata_5),
			.o_ecc_fail             (ecc_fail_5));

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
		set_por();
		#1us;
		enable_clk = 1'b1;
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

	`SVUNIT_TESTS_BEGIN
	begin

		//** 16 Bit generic ecc register

		#1us;
		waccess_16 <= 1'b0;
		raccess_16 <= 1'b0;
		#1us;
		`SVTEST("check write/read without ECC correction")
		`FAIL_UNLESS_EQUAL(ecc_fail_16, 1'b0)
		waccess_16 <= 1'b1;
		raccess_16 <= 1'b0;
		wdata_16   <= 16'hAFFE;
		wait_for_n_clocks(1);
		`FAIL_UNLESS_EQUAL(ecc_fail_16, 1'b0)
		waccess_16 <= 1'b0;
		raccess_16 <= 1'b1;
		wait_for_n_clocks(1);
		`FAIL_UNLESS_EQUAL(ecc_fail_16, 1'b0)
		`FAIL_UNLESS_EQUAL(rdata_16, 16'hAFFE)
		waccess_16 <= 1'b0;
		raccess_16 <= 1'b0;
		#1us;
		`SVTEST_END

		#1us;
		waccess_16 <= 1'b0;
		raccess_16 <= 1'b0;
		#1us;
		`SVTEST("check write/read without ECC correction")
		`FAIL_UNLESS_EQUAL(ecc_fail_16, 1'b0)
		waccess_16 <= 1'b1;
		raccess_16 <= 1'b0;
		wdata_16   <= 16'h1234;
		wait_for_n_clocks(1);
		`FAIL_UNLESS_EQUAL(ecc_fail_16, 1'b0)
		waccess_16 <= 1'b0;
		raccess_16 <= 1'b1;
		wait_for_n_clocks(1);
		`FAIL_UNLESS_EQUAL(ecc_fail_16, 1'b0)
		`FAIL_UNLESS_EQUAL(rdata_16, 16'h1234)
		waccess_16 <= 1'b0;
		raccess_16 <= 1'b0;
		#1us;
		`SVTEST_END

		#1us;
		waccess_16 <= 1'b0;
		raccess_16 <= 1'b0;
		#1us;
		`SVTEST("check write/read with 1 Bit ECC correction at different time")
		`FAIL_UNLESS_EQUAL(ecc_fail_16, 1'b0)
		waccess_16 <= 1'b1;
		raccess_16 <= 1'b0;
		wdata_16   <= 16'h5678;
		wait_for_n_clocks(1);
		`FAIL_UNLESS_EQUAL(ecc_fail_16, 1'b0)
		force i_ecc_register_16.data_reg = 16'h5679;
		waccess_16 <= 1'b0;
		raccess_16 <= 1'b0;
		wait_for_n_clocks(1);
		waccess_16 <= 1'b0;
		raccess_16 <= 1'b1;
		wait_for_n_clocks(1);
		`FAIL_UNLESS_EQUAL(ecc_fail_16, 1'b0)
		`FAIL_UNLESS_EQUAL(rdata_16, 16'h5678)
		release i_ecc_register_16.data_reg;
		waccess_16 <= 1'b0;
		raccess_16 <= 1'b0;
		#1us;
		`SVTEST_END

		#1us;
		waccess_16 <= 1'b0;
		raccess_16 <= 1'b0;
		#1us;
		`SVTEST("check write/read with 2 Bit ECC correction at different time")
		`FAIL_UNLESS_EQUAL(ecc_fail_16, 1'b0)
		waccess_16 <= 1'b1;
		raccess_16 <= 1'b0;
		wdata_16   <= 16'h24CD;
		wait_for_n_clocks(1);
		`FAIL_UNLESS_EQUAL(ecc_fail_16, 1'b0)
		force i_ecc_register_16.data_reg = 16'h24CE;
		waccess_16 <= 1'b0;
		raccess_16 <= 1'b0;
		wait_for_n_clocks(1);
		waccess_16 <= 1'b0;
		raccess_16 <= 1'b1;
		wait_for_n_clocks(1);
		`FAIL_UNLESS_EQUAL(ecc_fail_16, 1'b1)
		`FAIL_UNLESS_EQUAL(rdata_16, 16'h24CE)
		release i_ecc_register_16.data_reg;
		waccess_16 <= 1'b0;
		raccess_16 <= 1'b0;
		#1us;
		`SVTEST_END

		#1us;
		waccess_16 <= 1'b0;
		raccess_16 <= 1'b0;
		#1us;
		`SVTEST("check write/read with 1 Bit ECC correction at the same time")
		`FAIL_UNLESS_EQUAL(ecc_fail_16, 1'b0)
		waccess_16 <= 1'b1;
		raccess_16 <= 1'b1;
		wdata_16   <= 16'h54CD;
		wait_for_n_clocks(1);
		`FAIL_UNLESS_EQUAL(ecc_fail_16, 1'b0)
		force i_ecc_register_16.data_reg = 16'h54CF;
		wait_for_n_clocks(1);
		`FAIL_UNLESS_EQUAL(rdata_16, 16'h54CD)
		release i_ecc_register_16.data_reg;
		waccess_16 <= 1'b0;
		raccess_16 <= 1'b0;
		#1us;
		`SVTEST_END

		#1us;
		waccess_16 <= 1'b0;
		raccess_16 <= 1'b0;
		#1us;
		`SVTEST("check write/read with 2 Bit ECC correction at the same time")
		`FAIL_UNLESS_EQUAL(ecc_fail_16, 1'b0)
		waccess_16 <= 1'b1;
		raccess_16 <= 1'b1;
		wdata_16   <= 16'h24CD;
		wait_for_n_clocks(1);
		`FAIL_UNLESS_EQUAL(ecc_fail_16, 1'b0)
		force i_ecc_register_16.data_reg = 16'h24CE;
		wait_for_n_clocks(1);
		`FAIL_UNLESS_EQUAL(ecc_fail_16, 1'b1)
		`FAIL_UNLESS_EQUAL(rdata_16, 16'h24CE)
		release i_ecc_register_16.data_reg;
		waccess_16 <= 1'b0;
		raccess_16 <= 1'b0;
		#1us;
		`SVTEST_END

		//** 5 Bit generic ecc register

		#1us;
		waccess_5 <= 1'b0;
		raccess_5 <= 1'b0;
		#1us;
		`SVTEST("check write/read without ECC correction")
		`FAIL_UNLESS_EQUAL(ecc_fail_5, 1'b0)
		waccess_5 <= 1'b1;
		raccess_5 <= 1'b0;
		wdata_5   <= 5'b11101;
		wait_for_n_clocks(1);
		`FAIL_UNLESS_EQUAL(ecc_fail_5, 1'b0)
		waccess_5 <= 1'b0;
		raccess_5 <= 1'b1;
		wait_for_n_clocks(1);
		`FAIL_UNLESS_EQUAL(ecc_fail_5, 1'b0)
		`FAIL_UNLESS_EQUAL(rdata_5, 5'b11101)
		waccess_5 <= 1'b0;
		raccess_5 <= 1'b0;
		#1us;
		`SVTEST_END

		#1us;
		waccess_5 <= 1'b0;
		raccess_5 <= 1'b0;
		#1us;
		`SVTEST("check write/read without ECC correction")
		`FAIL_UNLESS_EQUAL(ecc_fail_5, 1'b0)
		waccess_5 <= 1'b1;
		raccess_5 <= 1'b0;
		wdata_5   <= 5'b10001;
		wait_for_n_clocks(1);
		`FAIL_UNLESS_EQUAL(ecc_fail_5, 1'b0)
		waccess_5 <= 1'b0;
		raccess_5 <= 1'b1;
		wait_for_n_clocks(1);
		`FAIL_UNLESS_EQUAL(ecc_fail_5, 1'b0)
		`FAIL_UNLESS_EQUAL(rdata_5, 5'b10001)
		waccess_5 <= 1'b0;
		raccess_5 <= 1'b0;
		#1us;
		`SVTEST_END

		#1us;
		waccess_5 <= 1'b0;
		raccess_5 <= 1'b0;
		#1us;
		`SVTEST("check write/read with 1 Bit ECC correction at different time")
		`FAIL_UNLESS_EQUAL(ecc_fail_5, 1'b0)
		waccess_5 <= 1'b1;
		raccess_5 <= 1'b0;
		wdata_5   <= 5'b10011;
		wait_for_n_clocks(1);
		`FAIL_UNLESS_EQUAL(ecc_fail_5, 1'b0)
		force i_ecc_register_5.data_reg = 5'b10111;
		waccess_5 <= 1'b0;
		raccess_5 <= 1'b0;
		wait_for_n_clocks(1);
		waccess_5 <= 1'b0;
		raccess_5 <= 1'b1;
		wait_for_n_clocks(1);
		`FAIL_UNLESS_EQUAL(ecc_fail_5, 1'b0)
		`FAIL_UNLESS_EQUAL(rdata_5, 5'b10011)
		release i_ecc_register_5.data_reg;
		waccess_5 <= 1'b0;
		raccess_5 <= 1'b0;
		#1us;
		`SVTEST_END

		#1us;
		waccess_5 <= 1'b0;
		raccess_5 <= 1'b0;
		#1us;
		`SVTEST("check write/read with 2 Bit ECC correction at different time")
		`FAIL_UNLESS_EQUAL(ecc_fail_5, 1'b0)
		waccess_5 <= 1'b1;
		raccess_5 <= 1'b0;
		wdata_5   <= 5'b11001;
		wait_for_n_clocks(1);
		`FAIL_UNLESS_EQUAL(ecc_fail_5, 1'b0)
		force i_ecc_register_5.data_reg = 5'b11111;
		waccess_5 <= 1'b0;
		raccess_5 <= 1'b0;
		wait_for_n_clocks(1);
		waccess_5 <= 1'b0;
		raccess_5 <= 1'b1;
		wait_for_n_clocks(1);
		`FAIL_UNLESS_EQUAL(ecc_fail_5, 1'b1)
		`FAIL_UNLESS_EQUAL(rdata_5, 5'b11111)
		release i_ecc_register_5.data_reg;
		waccess_5 <= 1'b0;
		raccess_5 <= 1'b0;
		#1us;
		`SVTEST_END

		#1us;
		waccess_5 <= 1'b0;
		raccess_5 <= 1'b0;
		#1us;
		`SVTEST("check write/read with 1 Bit ECC correction at the same time")
		`FAIL_UNLESS_EQUAL(ecc_fail_5, 1'b0)
		waccess_5 <= 1'b1;
		raccess_5 <= 1'b1;
		wdata_5   <= 5'b00000;
		wait_for_n_clocks(1);
		`FAIL_UNLESS_EQUAL(ecc_fail_5, 1'b0)
		force i_ecc_register_5.data_reg = 5'b00001;
		wait_for_n_clocks(1);
		`FAIL_UNLESS_EQUAL(rdata_5, 5'b00000)
		release i_ecc_register_5.data_reg;
		waccess_5 <= 1'b0;
		raccess_5 <= 1'b0;
		#1us;
		`SVTEST_END

		#1us;
		waccess_5 <= 1'b0;
		raccess_5 <= 1'b0;
		#1us;
		`SVTEST("check write/read with 2 Bit ECC correction at the same time")
		`FAIL_UNLESS_EQUAL(ecc_fail_5, 1'b0)
		waccess_5 <= 1'b1;
		raccess_5 <= 1'b1;
		wdata_5   <= 5'b00011;
		wait_for_n_clocks(1);
		`FAIL_UNLESS_EQUAL(ecc_fail_5, 1'b0)
		force i_ecc_register_5.data_reg = 5'b11011;
		wait_for_n_clocks(1);
		`FAIL_UNLESS_EQUAL(ecc_fail_5, 1'b1)
		`FAIL_UNLESS_EQUAL(rdata_5, 5'b11011)
		release i_ecc_register_5.data_reg;
		waccess_5 <= 1'b0;
		raccess_5 <= 1'b0;
		#1us;
		`SVTEST_END

		end
		`SVUNIT_TESTS_END

		endmodule
