module spi_frames_testsuite;
  import svunit_pkg::svunit_testsuite;
  import common_pkg::*;
  import addresses_pkg::*;
  
  string name = "spi_frames_ts";
  svunit_testsuite svunit_ts;
  
  
  //===================================
  // These are the unit tests that we
  // want included in this testsuite
  //===================================
  spi_frames_test spi_frames_t();
  behaviour_checker_test behaviour_checker_t();
  tdma_scheme_upload_listener_test tdma_scheme_upload_listener_t();
  dsi3_master_transmission_checker_test dsi3_master_transmission_checker_t();

  //===================================
  // Build
  //===================================
  function void build();
  	$timeformat(-12, 0, "ps", 20);
	
	spi_frames_t.build();
	behaviour_checker_t.build();
	tdma_scheme_upload_listener_t.build();
	dsi3_master_transmission_checker_t.build();
	
    svunit_ts = new(name);
    svunit_ts.add_testcase(spi_frames_t.svunit_ut);
	svunit_ts.add_testcase(behaviour_checker_t.svunit_ut);
	svunit_ts.add_testcase(tdma_scheme_upload_listener_t.svunit_ut);
	svunit_ts.add_testcase(dsi3_master_transmission_checker_t.svunit_ut);
  endfunction


  //===================================
  // Run
  //===================================
  task run();
    svunit_ts.run();
	
	spi_frames_t.run();
	behaviour_checker_t.run();
	tdma_scheme_upload_listener_t.run();
	dsi3_master_transmission_checker_t.run();
	
    svunit_ts.report();
  endtask

endmodule
