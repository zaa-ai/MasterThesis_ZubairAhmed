module testrunner import project_pkg::*; ();
	import uvm_pkg::*;
	import svunit_pkg::svunit_testrunner;
	import svunit_uvm_mock_pkg::svunit_uvm_test_inst;
	import svunit_uvm_mock_pkg::uvm_report_mock;

	string name = "testrunner";
	svunit_testrunner svunit_tr;

	//==================================
	// These are the test suites that we
	// want included in this testrunner
	//==================================
	spi_frames_testsuite spi_ts();

	//===================================
	// Main
	//===================================
	initial	begin
		uvm_report_cb::add(null, uvm_report_mock::reports);
		build();
		svunit_uvm_test_inst("svunit_uvm_test");
		run();
		$finish();
	end

	//===================================
	// Build
	//===================================
	function void build();
		svunit_tr = new(name);
		spi_ts.build();
		svunit_tr.add_testsuite(spi_ts.svunit_ts);
	endfunction

	//===================================
	// Run
	//===================================
	task run();
		spi_ts.run();
		svunit_tr.report();
	endtask

endmodule
