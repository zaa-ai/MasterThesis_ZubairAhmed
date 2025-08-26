module spi_testsuite;
  import svunit_pkg::svunit_testsuite;
  import common_pkg::*;
  import addresses_pkg::*;
  
  string name = "spi_ts";
  svunit_testsuite svunit_ts;
  
  
  //===================================
  // These are the unit tests that we
  // want included in this testsuite
  //===================================
  spi_test	spi_t();

  //===================================
  // Build
  //===================================
  function void build();
  	$timeformat(-12, 0, "ps", 20);
  	spi_t.build();
    svunit_ts = new(name);
    svunit_ts.add_testcase(spi_t.svunit_ut);
  endfunction


  //===================================
  // Run
  //===================================
  task run();
    svunit_ts.run();
    spi_t.run();
    svunit_ts.report();
  endtask

endmodule
