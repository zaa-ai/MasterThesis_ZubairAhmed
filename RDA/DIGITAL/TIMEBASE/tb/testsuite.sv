module general_testsuite;
  import svunit_pkg::svunit_testsuite;
  
  string name = "general_ts";
  svunit_testsuite svunit_ts;
  
  //===================================
  // These are the unit tests that we
  // want included in this testsuite
  //===================================
  timebase_test timebase_ut();

  //===================================
  // Build
  //===================================
  function void build();
  	$timeformat(-12, 0, "ps", 20);
  	timebase_ut.build();
    svunit_ts = new(name);
    svunit_ts.add_testcase(timebase_ut.svunit_ut);
  endfunction


  //===================================
  // Run
  //===================================
  task run();
    svunit_ts.run();
    timebase_ut.run();
    svunit_ts.report();
  endtask

endmodule
