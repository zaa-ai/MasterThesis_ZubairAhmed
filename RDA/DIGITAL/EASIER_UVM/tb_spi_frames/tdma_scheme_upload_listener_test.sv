`include "uvm_macros.svh"
`include "svunit_defines.svh"

module tdma_scheme_upload_listener_test import project_pkg::*; ();
	
	import svunit_pkg::svunit_testcase;
	import svunit_uvm_mock_pkg::*;
	import spi_pkg::*;
	import common_env_pkg::*;
	import uvm_pkg::*;
	import spi_frames_unit_test_pkg::*;
	
	string name = "tdma_scheme_upload_listener_test";
	svunit_testcase svunit_ut;
	
	//===================================
	// This is the UUT that we're 
	// running the Unit Tests on
	//===================================
	
	top_config				m_top_config;
	
	initial begin
		uvm_config_db #(top_config)::get(null, "uvm_test_top", "m_top_config", m_top_config);
	end
	
	//===================================
	// Build
	//===================================
	function void build();
		svunit_ut = new(name);
	endfunction
		
	//===================================
	// Setup for running the Unit Tests
	//===================================
	task setup();
		svunit_ut.setup();
		uvm_report_mock::setup();
		for (int i=0; i<project_pkg::DSI_CHANNELS; i++) begin
			checker_config::get().enable_master_transmission_checker[i] = 1'b0;
		end
	endtask

	//===================================
	// Here we deconstruct anything we 
	// need after running the Unit Tests
	//===================================
	task teardown();
		svunit_ut.teardown();
	endtask
	
	//===================================
	// All tests are defined between the
	// SVUNIT_TESTS_BEGIN/END macros
	//
	// Each individual test must be
	// defined between `SVTEST(_NAME_)
	// `SVTEST_END
	//
	// i.e.
	//	 `SVTEST(mytest)
	//		 <test code>
	//	 `SVTEST_END
	//===================================
	
	function void upload_tdma_packet(logic[1:0] channels, int index, shortint unsigned earliest_start, shortint unsigned latest_end, int unsigned symbols, bit[1:0] id);
		spi_command_frame_seq frame;
		spi_upload_tdma_packet_seq upload_seq;
		spi_tx_crc_request_seq crc_seq;
		
		upload_seq = new();
		if(upload_seq.randomize() with {
				channel_bits == channels;
				packet_index == 4'(index);
				tdma_packet.earliest_start_time == earliest_start;
				tdma_packet.latest_start_time == latest_end;
				tdma_packet.symbol_count == symbols;
				tdma_packet.id_symbol_count == id;
				} == 0) `ERROR("failed to randomize");
		
		crc_seq = new();
		if(crc_seq.randomize() with { mosi_crc_correct == 1'b1;} == 0) `ERROR("failed to randomize");
		
		frame = new();
		frame.add_command(upload_seq);
		frame.add_command(crc_seq);
		
		m_top_config.m_tdma_scheme_upload_listener.write(frame);
	endfunction
	
	function void validate_tdma_scheme(logic[1:0] channels, int packets, int period);
		spi_command_frame_seq frame;
		spi_validate_tdma_scheme_seq validate_seq;
		spi_tx_crc_request_seq crc_seq;
		
		validate_seq = new();
		if(validate_seq.randomize() with {
				channel_bits == channels;
				packet_count == 4'(packets);
				pdcm_period == 16'(period);
				} == 0) `ERROR("failed to randomize");
		
		crc_seq = new();
		if(crc_seq.randomize() with { mosi_crc_correct == 1'b1;} == 0) `ERROR("failed to randomize");
		
		frame = new();
		frame.add_command(validate_seq);
		frame.add_command(crc_seq);
		
		m_top_config.m_tdma_scheme_upload_listener.write(frame);
	endfunction
	
	`SVUNIT_TESTS_BEGIN

		`SVTEST ("valid_two_packets_upload_single_channel_test")
			m_top_config.clear();
			
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[0].valid, 1'b0)
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[1].valid, 1'b0)
			
			upload_tdma_packet(2'b01, 0,  30,  70, 8, 2);
			upload_tdma_packet(2'b01, 1, 152, 192, 16, 1);
			validate_tdma_scheme(2'b01, 2, 300);
			
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[0].valid, 1'b1)
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[1].valid, 1'b0)
			
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[0].packets[0].earliest_start_time, 30)
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[0].packets[0].latest_start_time, 70)
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[0].packets[0].symbol_count, 8)
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[0].packets[0].id_symbol_count, 2)
			
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[0].packets[1].earliest_start_time, 152)
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[0].packets[1].latest_start_time, 192)
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[0].packets[1].symbol_count, 16)
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[0].packets[1].id_symbol_count, 1)
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[0].pdcm_period, 300)
				
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[0].get_packet_count(), 2)
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[1].get_packet_count(), 0)
		`SVTEST_END
	
		`SVTEST ("valid_denso_upload_test")
			m_top_config.clear();
			
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[0].valid, 1'b0)
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[1].valid, 1'b0)
			
			upload_tdma_packet(2'b11, 0,  30,  70, 8, 2);
			upload_tdma_packet(2'b11, 1, 152, 192, 8, 2);
			upload_tdma_packet(2'b11, 2, 274, 314, 8, 2);
			upload_tdma_packet(2'b11, 3, 396, 436, 8, 2);
			upload_tdma_packet(2'b11, 4, 518, 558, 8, 2);
			upload_tdma_packet(2'b11, 5, 640, 680, 8, 2);
			upload_tdma_packet(2'b11, 6, 758, 806, 8, 2);
			validate_tdma_scheme(2'b11, 7, 1000);
			
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[0].valid, 1'b1)
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[1].valid, 1'b1)
			
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[0].get_packet_count(), 7)
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[1].get_packet_count(), 7)
		`SVTEST_END
		
		`SVTEST ("invalid_two_packets_upload_too_few_symbols_test")
			m_top_config.clear();
			
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[0].valid, 1'b0)
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[1].valid, 1'b0)
			
			upload_tdma_packet(2'b01, 0,  30,  70, 8, 2);
			upload_tdma_packet(2'b01, 1, 152, 192, 3, 1); // only 3 symbols
			validate_tdma_scheme(2'b01, 2, 300);
			
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[0].valid, 1'b0)
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[1].valid, 1'b0)
		`SVTEST_END
		
		`SVTEST ("invalid_two_packets_upload_wrong_start_end_test")
			m_top_config.clear();
			
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[0].valid, 1'b0)
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[1].valid, 1'b0)
			
			upload_tdma_packet(2'b01, 0,  70,  30, 8, 2); // end before start time
			upload_tdma_packet(2'b01, 1, 152, 192, 8, 1); 
			validate_tdma_scheme(2'b01, 2, 300);
			
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[0].valid, 1'b0)
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[1].valid, 1'b0)
		`SVTEST_END
		
		`SVTEST ("invalid_two_packets_upload_wrong_start_end_test")
			m_top_config.clear();
			
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[0].valid, 1'b0)
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[1].valid, 1'b0)
			
			upload_tdma_packet(2'b01, 0, 152, 192, 8, 1); // wrong chronological order
			upload_tdma_packet(2'b01, 1,  70,  30, 8, 2);
			validate_tdma_scheme(2'b01, 2, 300);
			
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[0].valid, 1'b0)
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[1].valid, 1'b0)
		`SVTEST_END
		
		`SVTEST ("minimum_pdcm_period_test")
			m_top_config.clear();
			
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[0].valid, 1'b0)
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[1].valid, 1'b0)
			
			upload_tdma_packet(2'b11, 0, 30,  70, 8, 2);
			validate_tdma_scheme(2'b11, 1, 20); // period lower than 100
			
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[0].valid, 1'b1)
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[0].pdcm_period, 100)
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[1].valid, 1'b1)
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[1].pdcm_period, 100)
		`SVTEST_END
		
		`SVTEST ("latest_start_time_greater_than_period_test")
			m_top_config.clear();
			
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[0].valid, 1'b0)
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[1].valid, 1'b0)
			
			upload_tdma_packet(2'b11, 0, 450, 550, 8, 2); // latest start time greater than period
			validate_tdma_scheme(2'b11, 1, 500);
			
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[0].valid, 1'b0)
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[1].valid, 1'b0)
		`SVTEST_END

		`SVTEST ("all_start_times_greater_than_period_test")
			m_top_config.clear();
			
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[0].valid, 1'b0)
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[1].valid, 1'b0)
			
			upload_tdma_packet(2'b11, 0, 550, 570, 8, 2); // all start times greater than period
			validate_tdma_scheme(2'b11, 1, 500); 
			
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[0].valid, 1'b0)
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[1].valid, 1'b0)
		`SVTEST_END
		
		
		`SVTEST ("maximum_pdcm_period_test")
			m_top_config.clear();
			
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[0].valid, 1'b0)
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[1].valid, 1'b0)
			
			upload_tdma_packet(2'b11, 0,  30,  70, 8, 2);
			validate_tdma_scheme(2'b11, 1, 'hFFFF); // period lower than max
			
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[0].valid, 1'b1)
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[0].pdcm_period, 'hFFF0)
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[1].valid, 1'b1)
			`FAIL_UNLESS_EQUAL(tdma_scheme_upload_listener::schemes[1].pdcm_period, 'hFFF0)
		`SVTEST_END
		
	`SVUNIT_TESTS_END

endmodule
