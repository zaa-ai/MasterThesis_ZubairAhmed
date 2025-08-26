`ifdef RUN_SVUNIT_WITH_UVM
//  import uvm_pkg::*; this produces a Lint warning -> moved down (or is there any reason for having the import statement on top of the file?)
`endif

module testrunner import project_pkg::*; ();
  import svunit_pkg::svunit_testrunner;
`ifdef RUN_SVUNIT_WITH_UVM
  import uvm_pkg::*;
  import svunit_uvm_mock_pkg::svunit_uvm_test_inst;
  import svunit_uvm_mock_pkg::uvm_report_mock;
`endif

  string name = "easier UVM testrunner";
  svunit_testrunner svunit_tr;


  //==================================
  // These are the test suites that we
  // want included in this testrunner
  //==================================
  easier_uvm_testsuite easier_uvm_ts();


  //===================================
  // Main
  //===================================
  initial
  begin

    `ifdef RUN_SVUNIT_WITH_UVM_REPORT_MOCK
      uvm_report_cb::add(null, uvm_report_mock::reports);
    `endif

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
    easier_uvm_ts.build();
    svunit_tr.add_testsuite(easier_uvm_ts.svunit_ts);
  endfunction


  //===================================
  // Run
  //===================================
  task run();
  	easier_uvm_ts.run();
    svunit_tr.report();
  endtask


endmodule
