`include "svunit_defines.svh"

module crc_calculation_pkg_test import project_pkg::*; ();
	import svunit_pkg::svunit_testcase;
	
	string name = "crc_calculation_pkg_test";
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
		
		`SVTEST ("calculate_crc_test")
			`FAIL_UNLESS_EQUAL(crc_calculation_pkg::spi_calculate_crc(1'b1, {16'h5001, 16'hdec0}), 16'h29af)
			`FAIL_IF_EQUAL(    crc_calculation_pkg::spi_calculate_crc(1'b0, {16'h5001, 16'hdec0}), 16'h29af)
		`SVTEST_END
		
		//=============================================================================
			
		`SVTEST ("calculate_correct_crc_test")
			`FAIL_UNLESS_EQUAL(crc_calculation_pkg::spi_calculate_correct_crc({16'h5001, 16'hdec0}), 16'h29af)
		`SVTEST_END
		
		//=============================================================================
			
		`SVTEST ("ends_with_correct_crc_test")
			`FAIL_UNLESS_EQUAL(crc_calculation_pkg::spi_ends_with_correct_crc({16'h5001, 16'hdec0, 16'h29af}), 1'b1)	
			`FAIL_UNLESS_EQUAL(crc_calculation_pkg::spi_ends_with_correct_crc({16'h5001, 16'hdec0, 16'h0bad}), 1'b0)
		`SVTEST_END
		
		//=============================================================================
	
		`SVTEST ("crc_ccitt_test")
			// check CRC for correct values of common_pkg::crc_ccitt function
			`FAIL_UNLESS_EQUAL(crc_calculation_pkg::spi_crc_ccitt_16('{16'h405f, 16'h1234, 16'h0000}), 16'h8b65);
			`FAIL_UNLESS_EQUAL(crc_calculation_pkg::spi_crc_ccitt_16('{16'hc1f5, 16'h5678, 16'h0000}), 16'h12f4);
			`FAIL_UNLESS_EQUAL(crc_calculation_pkg::spi_crc_ccitt_16('{16'h83ff, 16'h029a, 16'hbcff, 16'h0000}), 16'h597f);
			`FAIL_UNLESS_EQUAL(crc_calculation_pkg::spi_crc_ccitt_16('{16'h87ff, 16'h0d00, 16'h00ff, 16'h0000}), 16'h6fa8);
		`SVTEST_END
		
		//=============================================================================
	
		`SVTEST ("miso_crc_example")
			logic[15:0] mosi_crc = crc_calculation_pkg::spi_calculate_correct_crc({16'h5102, 16'h0071, 16'h5103, 16'h03e7, 16'h1000});
			logic[15:0] miso_crc = crc_calculation_pkg::spi_calculate_correct_crc({16'h0000, 16'h5102, 16'h0071, 16'h5103, 16'h03e7});
			
			$display("---------------------");
			$display("MOSI CRC: %04h", mosi_crc);
			$display("MISO CRC: %04h", miso_crc);
			$display("---------------------");
			
			`FAIL_UNLESS_EQUAL(mosi_crc, 16'hf47f)
			`FAIL_UNLESS_EQUAL(miso_crc, 16'h38ff)
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("another_crc_example")
			logic[15:0] mosi_crc = crc_calculation_pkg::spi_calculate_correct_crc({16'h8d5c, 16'h915d, 16'hd5fe, 16'hffff, 16'h1709});
			logic[15:0] miso_crc = crc_calculation_pkg::spi_calculate_correct_crc({16'h0c00, 16'h8d5c, 16'h915d, 16'hd5fe, 16'hffff});
			
			$display("---------------------");
			$display("MOSI CRC: %04h", mosi_crc);
			$display("MISO CRC: %04h", miso_crc);
			$display("---------------------");
			
			`FAIL_UNLESS_EQUAL(mosi_crc, 16'h2b3c)
			`FAIL_UNLESS_EQUAL(miso_crc, 16'h5b08)
		`SVTEST_END
	
	`SVUNIT_TESTS_END

endmodule
