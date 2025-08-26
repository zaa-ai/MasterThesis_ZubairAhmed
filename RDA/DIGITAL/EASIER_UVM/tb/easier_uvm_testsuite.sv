module easier_uvm_testsuite;
  import svunit_pkg::svunit_testsuite;
  import common_pkg::*;
  import addresses_pkg::*;
  
  string name = "easier_uvm_ts";
  svunit_testsuite svunit_ts;
  
  
  //===================================
  // These are the unit tests that we
  // want included in this testsuite
  //===================================
  spi_sequences_test spi_sequences();
  spi_protocol_listener_test spi_protocol_listener();
  crc_calculation_pkg_test crc_package();
  otp_writer_test otp_writer();
  flags_container_test flags();
  dsi3_packets_test dsi3_packets();
  tdma_scheme_test tdma_schemes();

  //===================================
  // Build
  //===================================
  function void build();
  	$timeformat(-12, 0, "ps", 20);
  	
  	spi_sequences.build();
    spi_protocol_listener.build();
    crc_package.build();
    otp_writer.build();
    flags.build();
    dsi3_packets.build();
	tdma_schemes.build();
	
    svunit_ts = new(name);
    svunit_ts.add_testcase(spi_sequences.svunit_ut);
    svunit_ts.add_testcase(spi_protocol_listener.svunit_ut);
    svunit_ts.add_testcase(crc_package.svunit_ut);
    svunit_ts.add_testcase(otp_writer.svunit_ut);
    svunit_ts.add_testcase(flags.svunit_ut);
    svunit_ts.add_testcase(dsi3_packets.svunit_ut);
	svunit_ts.add_testcase(tdma_schemes.svunit_ut);
  endfunction

  //===================================
  // Run
  //===================================
  task run();
    svunit_ts.run();
    
    spi_sequences.run();
    spi_protocol_listener.run();
    crc_package.run();
    otp_writer.run();
    flags.run();
    dsi3_packets.run();
	tdma_schemes.run();
    
    svunit_ts.report();
  endtask

endmodule
