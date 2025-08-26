`include "uvm_macros.svh"
`include "svunit_defines.svh"

module behaviour_checker_test import project_pkg::*; ();
	
	import svunit_pkg::svunit_testcase;
	import svunit_uvm_mock_pkg::*;
	import spi_pkg::*;
	import common_env_pkg::*;
	import uvm_pkg::*;
	import spi_frames_unit_test_pkg::*;
	
	string name = "behaviour_checker_test";
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
	
	function void write_frame(spi_command_frame_seq frame);
		m_top_config.m_behaviour_checker.write(frame);
	endfunction
	
	`SVUNIT_TESTS_BEGIN
	
		`SVTEST ("no_error_test")
			m_top_config.clear();
			send_spi_tr(m_top_config.m_spi_protocol_listener,
						{16'h5001, 16'hdec0, 16'h1000, 16'haffe}, 
						{16'h0000, 16'h5001, 16'hdec0, 16'ha37f});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_frame_subscriber.frames.size(), 1)
			
			write_frame(m_top_config.m_spi_frame_subscriber.frames[0]);
			`FAIL_IF(!uvm_report_mock::verify_complete());
		`SVTEST_END
	
		//=============================================================================
		
		`SVTEST ("wrong_queue_size_error_too_few_outputs")
			spi_command_frame_seq frame;
			
			m_top_config.clear();
			send_spi_tr(m_top_config.m_spi_protocol_listener,
							{16'h5001, 16'hdec0, 16'h1000, 16'haffe}, 
							{16'h0000, 16'h5001, 16'hdec0, 16'ha37f});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_frame_subscriber.frames.size(), 1)
			frame = m_top_config.m_spi_frame_subscriber.frames[0];
			frame.data_out.pop_back();
			
			uvm_report_mock::expect_error("behaviour_checker", "Input data queue size 4 of frame is not equal to output data queue size 3.");
			write_frame(frame);
			`FAIL_IF(!uvm_report_mock::verify_complete());
		`SVTEST_END
		
		//=============================================================================
			
		`SVTEST ("wrong_queue_size_error_too_few_inputs")
			spi_command_frame_seq frame;
			
			m_top_config.clear();
			send_spi_tr(m_top_config.m_spi_protocol_listener,
							{16'h5001, 16'hdec0, 16'h1000, 16'haffe}, 
							{16'h0000, 16'h5001, 16'hdec0, 16'ha37f});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_frame_subscriber.frames.size(), 1)
			frame = m_top_config.m_spi_frame_subscriber.frames[0];
			frame.data_in.pop_back();
			
			uvm_report_mock::expect_error("behaviour_checker", "Input data queue size 3 of frame is not equal to output data queue size 4.");
			write_frame(frame);
			`FAIL_IF(!uvm_report_mock::verify_complete());
		`SVTEST_END
		
		//=============================================================================
						
		`SVTEST ("single_command_mirror_error")
			m_top_config.clear();
			send_spi_tr(m_top_config.m_spi_protocol_listener,
							{16'h5001, 16'hdec0, 16'h1000, 16'haffe}, 
							{16'h0000, 16'h0000, 16'hdec0, 16'he174});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_frame_subscriber.frames.size(), 1)
			
			uvm_report_mock::expect_error("behaviour_checker", "Mirroring error: 1. word 0x5001 of 1. command has not been mirrored (output data is 0x0000)");
			write_frame(m_top_config.m_spi_frame_subscriber.frames[0]);
			`FAIL_IF(!uvm_report_mock::verify_complete());
		`SVTEST_END
		
		//=============================================================================
			
		`SVTEST ("single_command_data_mirror_error")
			m_top_config.clear();
			send_spi_tr(m_top_config.m_spi_protocol_listener,
							{16'h5001, 16'hdec0, 16'h1000, 16'h1234}, 
							{16'h0000, 16'h5001, 16'haffe, 16'h4f8a});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_frame_subscriber.frames.size(), 1)
			
			uvm_report_mock::expect_error("behaviour_checker", "Mirroring error: 2. word 0xdec0 of 1. command has not been mirrored (output data is 0xaffe)");
			write_frame(m_top_config.m_spi_frame_subscriber.frames[0]);
			`FAIL_IF(!uvm_report_mock::verify_complete());
		`SVTEST_END
		
		//=============================================================================
			
		`SVTEST ("multiple_commands_no_mirror_error")
			m_top_config.clear();
			send_spi_tr(m_top_config.m_spi_protocol_listener,
					{16'h5001, 16'hdec0, 16'h8c00, 16'h1234, 16'h5678, 16'h1000, 16'haffe}, 
					{16'h0000, 16'h5001, 16'hdec0, 16'h8c00, 16'h1234, 16'h5678, 16'h3c58});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_frame_subscriber.frames.size(), 1)
			
			write_frame(m_top_config.m_spi_frame_subscriber.frames[0]);
			`FAIL_IF(!uvm_report_mock::verify_complete());
		`SVTEST_END
		
		//=============================================================================
			
		`SVTEST ("multiple_commands_command_mirror_error")
			
			m_top_config.clear();
			send_spi_tr(m_top_config.m_spi_protocol_listener,
					{16'h5001, 16'hdec0, 16'h8c00, 16'h1234, 16'h5678, 16'h1000, 16'haffe}, 
					{16'h0000, 16'h5001, 16'hdec0, 16'haffe, 16'h1234, 16'h5678, 16'h374e});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_frame_subscriber.frames.size(), 1)
			uvm_report_mock::expect_error("behaviour_checker", "Mirroring error: 1. word 0x8c00 of 2. command has not been mirrored (output data is 0xaffe)");
			
			write_frame(m_top_config.m_spi_frame_subscriber.frames[0]);
			`FAIL_IF(!uvm_report_mock::verify_complete());
		`SVTEST_END
		
		//=============================================================================

		`SVTEST ("multiple_commands_data_mirror_error")
			m_top_config.clear();
			send_spi_tr(m_top_config.m_spi_protocol_listener,
					{16'h5001, 16'hdec0, 16'h8c00, 16'h1234, 16'h5678, 16'h1000, 16'haffe}, 
					{16'h0000, 16'h5001, 16'hdec0, 16'h8c00, 16'h1234, 16'hffff, 16'h7ad1});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_frame_subscriber.frames.size(), 1)
			
			uvm_report_mock::expect_error("behaviour_checker", "Mirroring error: 3. word 0x5678 of 2. command has not been mirrored (output data is 0xffff)");
			write_frame(m_top_config.m_spi_frame_subscriber.frames[0]);
			`FAIL_IF(!uvm_report_mock::verify_complete());
		`SVTEST_END	
		
		//=============================================================================

		`SVTEST ("read_dsi_data_no_mirror_error")
			spi_read_crm_data_packets_seq read_seq;
			spi_tx_crc_request_seq crc_seq;
			spi_command_frame_seq frame;
			
			m_top_config.clear();
			send_spi_tr(m_top_config.m_spi_protocol_listener,
					{16'h3400, 16'h3000, 16'h3000, 16'h3000, 16'h1000, 16'h9b3f}, 
					{16'h0001, 16'h3400, 16'h5008, 16'h0b64, 16'h3df5, 16'hc436});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_frame_subscriber.frames.size(), 1)
			frame = m_top_config.m_spi_frame_subscriber.frames[0];
			
			`FAIL_UNLESS_EQUAL(frame.commands.size(), 2);
			`FAIL_UNLESS_EQUAL($cast(read_seq,frame.commands[0]), 1)
			`FAIL_UNLESS_EQUAL($cast(crc_seq, frame.commands[1]), 1)
			
			write_frame(frame);
			`FAIL_IF(!uvm_report_mock::verify_complete());
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("reset_command_no_error_test")
			m_top_config.clear();
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener,
						{16'hCC01, 16'hFFFF, 16'hFFFF, 16'hFFFF, 16'hFFFF, 16'hCC03, 16'h1000}, 
						{16'h0C00, 16'hCC01, 16'hFFFF, 16'hFFFF, 16'hFFFF, 16'h0C00, 16'hCC03});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_frame_subscriber.frames.size(), 2)
			
			write_frame(m_top_config.m_spi_frame_subscriber.frames[0]);
			write_frame(m_top_config.m_spi_frame_subscriber.frames[1]);
			
			`FAIL_IF(!uvm_report_mock::verify_complete());
		`SVTEST_END

	`SVUNIT_TESTS_END

endmodule
