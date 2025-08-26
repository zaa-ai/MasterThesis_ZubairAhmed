module testsuite;
  import svunit_pkg::svunit_testsuite;
  
  string name = "ts";
  svunit_testsuite svunit_ts;
  
  //===================================
  // These are the unit tests that we
  // want included in this testsuite
  //===================================
  test	ut();

  //===================================
  // Build
  //===================================
  function void build();
  	$timeformat(-12, 0, "ps", 20);
  	ut.build();
    svunit_ts = new(name);
    svunit_ts.add_testcase(ut.svunit_ut);
  endfunction


  //===================================
  // Run
  //===================================
  task run();
    svunit_ts.run();
    ut.run();
    svunit_ts.report();
  endtask

endmodule
