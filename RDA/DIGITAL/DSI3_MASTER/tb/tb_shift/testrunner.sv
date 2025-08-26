module testrunner import project_pkg::*; ();
	import svunit_pkg::svunit_testrunner;

	string name = "testrunner";
	svunit_testrunner svunit_tr;


	//==================================
	// These are the test suites that we
	// want included in this testrunner
	//==================================
	testsuite ts();


	//===================================
	// Main
	//===================================
	initial
	begin

		build();

		`ifdef RUN_SVUNIT_WITH_UVM
			svunit_uvm_test_inst("svunit_uvm_test");
		`endif

		run();
		$finish();
	end


	//===================================
	// Build
	//===================================
	function void build();
		svunit_tr = new(name);
		ts.build();
		svunit_tr.add_testsuite(ts.svunit_ts);
	endfunction


	//===================================
	// Run
	//===================================
	task run();
		ts.run();
		svunit_tr.report();
	endtask


endmodule
