`include "svunit_defines.svh"

module tdma_scheme_test import project_pkg::*; ();
	import svunit_pkg::svunit_testcase;
	
	import spi_pkg::*;
	import common_pkg::*;
	import common_env_pkg::*;
	
	string name = "tdma_scheme_test";
	svunit_testcase svunit_ut;
	
	//===================================
	// This is the UUT that we're 
	// running the Unit Tests on
	//===================================
	
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
	
	function void print_tdma_scheme(tdma_scheme_pdcm scheme);
		`INFO(scheme.convert2string());
	endfunction
	
	`SVUNIT_TESTS_BEGIN
	
		`SVTEST ("tdma_scheme_pdcm_random_test")
			repeat(10) begin
				tdma_scheme_pdcm scheme = new();
				`FAIL_IF_EQUAL(scheme.randomize() with {packets.size() > 0; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}, 0);
				print_tdma_scheme(scheme);
				`FAIL_UNLESS_EQUAL(scheme.is_valid(scheme.get_packet_count()), 1'b1)
			end
		`SVTEST_END

		`SVTEST ("tdma_scheme_pdcm_small_test")
			repeat(10) begin
				tdma_scheme_pdcm scheme = new();
				`FAIL_IF_EQUAL(scheme.randomize() with {packets.size() == 4; symbol_count_min==4; symbol_count_max==8;}, 0);
				print_tdma_scheme(scheme);
				`FAIL_UNLESS_EQUAL(scheme.is_valid(scheme.get_packet_count()), 1'b1)
			end
		`SVTEST_END
		
		`SVTEST ("tdma_scheme_pdcm_denso_is_valid_test")
			tdma_scheme_pdcm_denso scheme = new();
			`FAIL_UNLESS_EQUAL(scheme.is_valid(scheme.get_packet_count()), 1'b1)
		`SVTEST_END

		`SVTEST ("tdma_scheme_pdcm_denso_is_valid_too_few_packets_test")
			tdma_scheme_pdcm_denso scheme = new();
			`FAIL_IF_EQUAL(scheme.is_valid(8), 1'b1)
		`SVTEST_END

		`SVTEST ("tdma_scheme_pdcm_denso_16_is_valid_test")
			tdma_scheme_pdcm_denso scheme = new();
			`FAIL_UNLESS_EQUAL(scheme.is_valid(scheme.get_packet_count()), 1'b1)
		`SVTEST_END

		`SVTEST ("tdma_scheme_empty_default_is_valid_zero_packets_test")
			tdma_scheme_empty_default scheme = new();
			`FAIL_IF_EQUAL(scheme.is_valid(0), 1'b1)
		`SVTEST_END
		
		`SVTEST ("tdma_scheme_pdcm_is_valid_zero_packets_test")
			tdma_scheme_pdcm_denso scheme = new();
			`FAIL_IF_EQUAL(scheme.is_valid(0), 1'b1)
		`SVTEST_END
			
	`SVUNIT_TESTS_END

endmodule
