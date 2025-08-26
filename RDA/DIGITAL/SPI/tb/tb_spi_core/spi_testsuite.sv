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
  spi_core_test	spi_ct();
  buffer_writer_access_arbiter_test arbiter_test ();

  //===================================
  // Build
  //===================================
  function void build();
  	$timeformat(-12, 0, "ps", 20);
    spi_ct.build();
    arbiter_test.build();
    svunit_ts = new(name);
    svunit_ts.add_testcase(spi_ct.svunit_ut);
  endfunction


  //===================================
  // Run
  //===================================
  task run();
    svunit_ts.run();
    spi_ct.run();
    arbiter_test.run();
    svunit_ts.report();
  endtask

endmodule
