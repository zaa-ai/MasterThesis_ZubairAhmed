`include "svunit_defines.svh"

module flags_container_test import project_pkg::*; ();
	import svunit_pkg::svunit_testcase;
	
	import spi_pkg::*;
	
	string name = "flags_container_test";
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
	`SVUNIT_TESTS_BEGIN
	
		`SVTEST ("basic_flags_test")
			flags_container #(dsi_response_flags) flags = new();
			
			flags.set_value(SE, 1'b1);
			flags.set_value(VE, 1'b1);
			
			`FAIL_UNLESS_EQUAL(flags.get_value(SCE), 1'b0)
			`FAIL_UNLESS_EQUAL(flags.get_value(CRC), 1'b0)
			`FAIL_UNLESS_EQUAL(flags.get_value(TE),  1'b0)
			`FAIL_UNLESS_EQUAL(flags.get_value(SE),  1'b1)
			`FAIL_UNLESS_EQUAL(flags.get_value(VE),  1'b1)
			`FAIL_UNLESS_EQUAL(flags.get_value(CE),  1'b0)
		`SVTEST_END
		
		`SVTEST ("set_values_test")
			flags_container #(dsi_response_flags) flags = new();
			
			flags.set_values(16'h3c00);
			
			`FAIL_UNLESS_EQUAL(flags.get_value(SCE), 1'b1)
			`FAIL_UNLESS_EQUAL(flags.get_value(CRC), 1'b1)
			`FAIL_UNLESS_EQUAL(flags.get_value(TE),  1'b1)
			`FAIL_UNLESS_EQUAL(flags.get_value(SE),  1'b1)
			`FAIL_UNLESS_EQUAL(flags.get_value(VE),  1'b0)
			`FAIL_UNLESS_EQUAL(flags.get_value(CE),  1'b0)
		`SVTEST_END
			
			
		`SVTEST ("set_flags_test")
			flags_container #(dsi_response_flags) flags = new();
			
			flags.set_flags({CRC});
			
			`FAIL_UNLESS_EQUAL(flags.get_value(SCE), 1'b0)
			`FAIL_UNLESS_EQUAL(flags.get_value(CRC), 1'b1)
			`FAIL_UNLESS_EQUAL(flags.get_value(TE),  1'b0)
			`FAIL_UNLESS_EQUAL(flags.get_value(SE),  1'b0)
			`FAIL_UNLESS_EQUAL(flags.get_value(VE),  1'b0)
			`FAIL_UNLESS_EQUAL(flags.get_value(CE),  1'b0)
		`SVTEST_END
			
		`SVTEST ("get_values_test")
			flags_container #(dsi_response_flags) flags = new();
			
			flags.set_flags({CRC});
			flags.set_flags({CE});
			
			`FAIL_UNLESS_EQUAL(flags.get_values(), 'h1100)
		`SVTEST_END
			
		`SVTEST ("check_value_pass_test")
			flags_container #(dsi_response_flags) flags = new();
			flags.set_values(16'h3c00);
			
			`FAIL_UNLESS_EQUAL(flags.check_value(SCE, 1'b1), 1'b0)
			`FAIL_UNLESS_EQUAL(flags.check_value(CRC, 1'b1), 1'b0)
			`FAIL_UNLESS_EQUAL(flags.check_value(TE,  1'b1), 1'b0)
			`FAIL_UNLESS_EQUAL(flags.check_value(SE,  1'b1), 1'b0)
			`FAIL_UNLESS_EQUAL(flags.check_value(VE,  1'b0), 1'b0)
			`FAIL_UNLESS_EQUAL(flags.check_value(CE,  1'b0), 1'b0)
		`SVTEST_END
			
		`SVTEST ("check_value_fail_test")
			flags_container #(dsi_response_flags) flags = new();
			flags.set_values(16'h3c00);
			
			`FAIL_UNLESS_EQUAL(flags.check_value(SCE, 1'b0), 1'b1)
			`FAIL_UNLESS_EQUAL(flags.check_value(CRC, 1'b0), 1'b1)
			`FAIL_UNLESS_EQUAL(flags.check_value(TE,  1'b0), 1'b1)
			`FAIL_UNLESS_EQUAL(flags.check_value(SE,  1'b0), 1'b1)
			`FAIL_UNLESS_EQUAL(flags.check_value(VE,  1'b1), 1'b1)
			`FAIL_UNLESS_EQUAL(flags.check_value(CE,  1'b1), 1'b1)
		`SVTEST_END
			
		`SVTEST ("check_flags_are_equal_pass_test")
			flags_container #(dsi_response_flags) flags = new();
			flags_container #(dsi_response_flags) expected = new();
			
			flags.set_values(16'h2400);
			expected.set_flags({SCE, SE});
			`FAIL_UNLESS_EQUAL(flags.check_flags_are_equal(expected), 1'b0)
		`SVTEST_END
			
		`SVTEST ("check_flags_are_equal_fail_test")
			flags_container #(dsi_response_flags) flags = new();
			flags_container #(dsi_response_flags) expected = new();
			
			expected.set_flags({SCE, CRC, SE});
			`FAIL_UNLESS_EQUAL(flags.check_flags_are_equal(expected), 1'b1)
		`SVTEST_END
			
		`SVTEST ("check_flags_are_equal_ignore_pass_test")
			flags_container #(dsi_response_flags) flags = new();
			flags_container #(dsi_response_flags) expected = new();
			
			flags.set_values(16'h3400);
			expected.set_flags({SCE, SE});
			`FAIL_UNLESS_EQUAL(flags.check_flags_are_equal(expected, .ignore_flags({CRC})), 1'b0)
		`SVTEST_END			

		`SVTEST ("check_flags_are_equal_ignore_fail_test")
			flags_container #(dsi_response_flags) flags = new();
			flags_container #(dsi_response_flags) expected = new();
			
			flags.set_values(16'h0900);
			expected.set_flags({TE});
			`FAIL_UNLESS_EQUAL(flags.check_flags_are_equal(expected, .ignore_flags({CE})), 1'b0)
			`FAIL_UNLESS_EQUAL(flags.check_flags_are_equal(expected, .ignore_flags({VE})), 1'b1)
		`SVTEST_END	
			
	`SVUNIT_TESTS_END

endmodule
