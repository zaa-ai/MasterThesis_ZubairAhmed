module testsuite;
  import svunit_pkg::svunit_testsuite;
  import common_pkg::*;
  import addresses_pkg::*;
  
  string name = "ts";
  svunit_testsuite svunit_ts;
  
  //===================================
  // These are the unit tests that we
  // want included in this testsuite
  //===================================
  dsi3_receiver_test	ut();
  dsi3_filter_test		fut();

  //===================================
  // Build
  //===================================
  function void build();
  	$timeformat(-12, 0, "ps", 20);
  	ut.build();
  	fut.build();
    svunit_ts = new(name);
    svunit_ts.add_testcase(ut.svunit_ut);
    svunit_ts.add_testcase(fut.svunit_ut);
  endfunction


  //===================================
  // Run
  //===================================
  task run();
    svunit_ts.run();
    ut.run();
    fut.run();
    svunit_ts.report();
  endtask

endmodule
