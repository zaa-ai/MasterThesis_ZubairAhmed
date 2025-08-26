`include "svunit_defines.svh"

module dsi3_master_transmission_checker_test import project_pkg::*; ();
	
	import svunit_pkg::svunit_testcase;
	import svunit_uvm_mock_pkg::*;
	import spi_pkg::*;
	import dsi3_master_pkg::*;
	import dsi3_slave_pkg::*;
	import common_pkg::*;
	import common_env_pkg::*;
	import uvm_pkg::*;
	import spi_frames_unit_test_pkg::*;
	
	string name = "dsi3_master_transmission_checker_test";
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
		m_top_config.clear();
		for (int i=0; i<project_pkg::DSI_CHANNELS; i++) begin
			checker_config::get().set_master_transmission_checker_enable(i, 1'b1);
			m_top_config.m_master_transmission_checker[i].reset_checker();
			m_top_config.m_master_transmission_checker[i].rfc = 1'b1;
			// set default configuration values
			m_top_config.m_master_transmission_checker[i].configuration_subscriber.bit_time = dsi3_pkg::BITTIME_8US;
			m_top_config.m_master_transmission_checker[i].configuration_subscriber.chip_time = 3;
			m_top_config.m_master_transmission_checker[i].configuration_subscriber.crc_en = 1;
			m_top_config.m_master_transmission_checker[i].configuration_subscriber.sync_pdcm = 1;
			m_top_config.m_master_transmission_checker[i].configuration_subscriber.sync_master = 0;
			m_top_config.m_master_transmission_checker[i].configuration_subscriber.crm_time = 450;
			m_top_config.m_master_transmission_checker[i].configuration_subscriber.crm_time_nr = 300;
		end
		
		`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, IDLE)
		`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].state, IDLE)
		#1us;
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
	
	task send_pdcm_pulse(logic[1:0] channels);
		dsi3_master_tr master_tr;
		
		master_tr = new();
		if(master_tr.randomize() with { msg_type == dsi3_pkg::PDCM;} == 0) `ERROR("failed to randomize");
		send_master_tr(channels, master_tr, 8us);
	endtask
	
	task send_crm_transmission(logic[1:0] channels, logic[15:0] words[$]);
		dsi3_master_tr master_tr;
		logic data[$];
		
		master_tr = new();
		if (convert_queue#(16, 1)::convert(words, data)) `ERROR("failed to convert queue");
		if(master_tr.randomize() with { msg_type == dsi3_pkg::CRM;} == 0) `ERROR("failed to randomize");
		master_tr.data = data;
		send_master_tr(channels, master_tr, (32 * 8us));
	endtask
		
	task send_master_tr(logic[1:0] channels, dsi3_master_tr master_tr, time end_time_offset);
		master_tr.bit_time = dsi3_pkg::BITTIME_8US;
		master_tr.begin_tr($time - end_time_offset);
		master_tr.end_tr($time);
		for (int i=0; i<project_pkg::DSI_CHANNELS; i++) begin
			if(channels[i] == 1'b1) m_top_config.m_master_transmission_checker[i].write_dsi3_master_tr(master_tr);
		end
	endtask
	
	task send_slave_response_words(logic[1:0] channels, logic[15:0] words[$]);
		logic[3:0] symbols[$];
		if (convert_queue#(16, 4)::convert(words, symbols)) `ERROR("failed to convert queue");
		send_slave_response(channels, symbols);
	endtask
	
	task send_slave_response(logic[1:0] channels, logic[3:0] symbols[$]);
		dsi3_slave_tr slave_tr;
		
		slave_tr = new();
		if(slave_tr.randomize() with { chiptime == 3; chips_per_symbol == 3; data.size() == symbols.size();} == 0) `ERROR("failed to randomize");
		foreach(slave_tr.data[i]) begin 
			slave_tr.data[i] = symbols[i];
		end
		slave_tr.begin_tr($time);
		slave_tr.end_tr($time + (3us * 3 * symbols.size()));
		for (int i=0; i<project_pkg::DSI_CHANNELS; i++) begin
			if(channels[i] == 1'b1) m_top_config.m_master_transmission_checker[i].write_dsi3_slave_tr(slave_tr);
		end
	endtask
	
	function dsi3_crm_packet create_crm_packet(logic valid_crc = 1'b1);
		dsi3_crm_packet packet;
		packet = new();
		if(packet.randomize() with { crc_correct == valid_crc;} == 0) `ERROR("failed to randomize");
		return packet;	
	endfunction
	
	function dsi3_pdcm_packet create_pdcm_packet(int symbol_count, dsi3_pkg::sid_length_e source_id, logic valid_crc = 1'b1);
		dsi3_pdcm_packet packet;
		packet = new();
		if(packet.randomize() with {data.size() == symbol_count; source_id_symbols == source_id; crc_correct == valid_crc;} == 0) `ERROR("failed to randomize");
		return packet;	
	endfunction
	
	task verify_uvm_errors();
		#10us;
		`FAIL_IF(!uvm_report_mock::verify_complete());
	endtask
	
	
	`SVUNIT_TESTS_BEGIN
	
		`SVTEST ("wait_test")
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, IDLE)
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].state, IDLE)
		
			// wait 500us
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'hDC00, 16'h01f4, 16'h1000},
																		{16'h0C00, 16'hDC00, 16'h01f4});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, WAIT)
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].state, WAIT)
			#400us;
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, WAIT)
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].state, WAIT)
			#150us;
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, IDLE)
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].state, IDLE)
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("stop_wait_by_clear_command_queue_test")
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, IDLE)
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].state, IDLE)
		
			// wait for maximum time
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'hDC00, 16'h7FFF, 16'h1000},
																		{16'h0C00, 16'hDC00, 16'h7FFF});
			
			#1ms;
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, WAIT)
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].state, WAIT)
			
			// clear DSI command queue
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h6C00, 16'h1000},
																		{16'h0C00, 16'h6C00});
			
			#10us;
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, IDLE)
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].state, IDLE)
			verify_uvm_errors();
		`SVTEST_END
	
		//=============================================================================
	
		`SVTEST ("unexpected_crm_transmission")
			send_crm_transmission(2'b11, {16'haffe, 16'hbeef});
						
			uvm_report_mock::expect_error("master_checker_0", "got CRM transmission without SPI request");
			uvm_report_mock::expect_error("master_checker_1", "got CRM transmission without SPI request");
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, IDLE)
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].state, IDLE)
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("unexpected_crm_transmission_after_reset_command")
		
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 
					{16'h8C00, 16'h1234, 16'h5678, 16'hFFFF, 16'hFFFF, 16'hFFFF, 16'hFFFF, 16'h1000},
					{16'h0C00, 16'h8C00, 16'h1234, 16'h5678, 16'hFFFF, 16'hFFFF, 16'hFFFF, 16'h0C00});
		
			send_crm_transmission(2'b11, {16'haffe, 16'hbeef});
						
			uvm_report_mock::expect_error("master_checker_0", "got CRM transmission without SPI request");
			uvm_report_mock::expect_error("master_checker_1", "got CRM transmission without SPI request");
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, IDLE)
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].state, IDLE)
			verify_uvm_errors();
		`SVTEST_END

		//=============================================================================
		
		`SVTEST ("unexpected_pdcm_transmission")
			set_tdma_scheme(2'b11, 300, {8}, {30}, {70});
			send_pdcm_pulse(2'b11);
						
			uvm_report_mock::expect_error("master_checker_0", "got PDCM pulse without SPI request");
			uvm_report_mock::expect_error("master_checker_1", "got PDCM pulse without SPI request");
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, IDLE)
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].state, IDLE)
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
	
		`SVTEST ("pdcm_transmission_without_valid_TDMA_scheme")
			set_tdma_scheme(2'b00, 300, {}, {}, {});
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'hCC03, 16'h1000},
																		{16'h0C00, 16'hCC03});
			send_pdcm_pulse(2'b11);
						
			uvm_report_mock::expect_error("master_checker_0", "got unexpected PDCM pulse without a valid TDMA scheme");
			uvm_report_mock::expect_error("master_checker_1", "got unexpected PDCM pulse without a valid TDMA scheme");
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, IDLE)
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].state, IDLE)
			verify_uvm_errors();
		`SVTEST_END
	
		//=============================================================================
	
		`SVTEST ("crm_without_errors_test")
			dsi3_crm_packet packet = create_crm_packet();
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h8C00, packet.get_word(0), 	packet.get_word(1), 16'h1000},
																		{16'h0C00, 16'h8C00, 			packet.get_word(0), packet.get_word(1)});

			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, WAIT_FOR_CRM)
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].state, WAIT_FOR_CRM)
			#10us;
			send_crm_transmission(2'b11, {packet.get_word(0), packet.get_word(1)});
			#500us;

			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, IDLE)
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].state, IDLE)
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("crm_without_errors_crc_disabled_test")
			m_top_config.m_master_transmission_checker[0].configuration_subscriber.crc_en = 0;
			m_top_config.m_master_transmission_checker[1].configuration_subscriber.crc_en = 0;
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h8C00, 16'h1234, 16'h5678, 16'h1000},
																		{16'h0C00, 16'h8C00, 16'h1234, 16'h5678});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, WAIT_FOR_CRM)
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].state, WAIT_FOR_CRM)

			send_crm_transmission(2'b11, {16'h1234, 16'h5678});
			#500us;
	
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, IDLE)
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].state, IDLE)
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("crm_read_data_without_error_test")
			dsi3_crm_packet request = create_crm_packet();
			dsi3_crm_packet crm_packet1 = create_crm_packet();
			dsi3_crm_packet crm_packet2 = create_crm_packet();
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h8C00, request.get_word(0), request.get_word(1), 16'h1000},
																		{16'h0C00, 16'h8C00, request.get_word(0), request.get_word(1)});
			
			fork			
				begin			
					send_crm_transmission(2'b11, {request.get_word(0), request.get_word(1)});
					#500us;
				end
				begin
					#30us;
					send_slave_response(2'b01, crm_packet1.data);
					send_slave_response(2'b10, crm_packet2.data);
				end
			join
		
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, IDLE)
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].state, IDLE)
			
			// read CRM data
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3400, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C03, 16'h3400, 16'h0008, crm_packet1.get_word(0), crm_packet1.get_word(1)});
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3800, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C02, 16'h3800, 16'h0008, crm_packet2.get_word(0), crm_packet2.get_word(1)});
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("crm_incomplete_read_data_without_error_test")
			dsi3_crm_packet request = create_crm_packet();
			dsi3_crm_packet crm_packet1 = create_crm_packet();
			dsi3_crm_packet crm_packet2 = create_crm_packet();
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h8C00, request.get_word(0), request.get_word(1), 16'h1000},
																		{16'h0C00, 16'h8C00, request.get_word(0), request.get_word(1)});
			
			fork			
				begin			
					send_crm_transmission(2'b11, {request.get_word(0), request.get_word(1)});
					#500us;
				end
				begin
					#30us;
					send_slave_response(2'b01, crm_packet1.data);
					send_slave_response(2'b10, crm_packet2.data);
				end
			join
		
			// read CRM data
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3400, 16'h1000},
					{16'h0C03, 16'h3400});
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3800, 16'h3000, 16'h1000},
					{16'h0C02, 16'h3800, 16'h0008});
			// expect no more CRM data
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3C00, 16'h3000, 16'h3000, 16'h3000, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C00, 16'h3C00, 16'h0000, 16'h0000, 16'h0000, 16'h0000, 16'h0000, 16'h0000});
			
			verify_uvm_errors();
		`SVTEST_END
				
		//=============================================================================
		
		`SVTEST ("crm_incomplete_read_clear_only_buffer_0_without_error_test")
			dsi3_crm_packet request = create_crm_packet();
			dsi3_crm_packet crm_packet1 = create_crm_packet();
			dsi3_crm_packet crm_packet2 = create_crm_packet();
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h8C00, request.get_word(0), request.get_word(1), 16'h1000},
																		{16'h0C00, 16'h8C00, request.get_word(0), request.get_word(1)});
			
			fork			
				begin			
					send_crm_transmission(2'b11, {request.get_word(0), request.get_word(1)});
					#500us;
				end
				begin
					#30us;
					send_slave_response(2'b01, crm_packet1.data);
					send_slave_response(2'b10, crm_packet2.data);
				end
			join
			
			// incomplete read CRM data -> second buffer must not be cleared
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3C00, 16'h1000},
					{16'h0C03, 16'h3C00});
			// expect no more CRM data
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3C00, 16'h3000, 16'h3000, 16'h3000, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C02, 16'h3C00, 16'h0000, 16'h0000, 16'h0000, 16'h0008, crm_packet2.get_word(0), crm_packet2.get_word(1)});
			
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("crm_incomplete_read_clear_both_buffers_without_error_test")
			dsi3_crm_packet request = create_crm_packet();
			dsi3_crm_packet crm_packet1 = create_crm_packet();
			dsi3_crm_packet crm_packet2 = create_crm_packet();
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h8C00, request.get_word(0), request.get_word(1), 16'h1000},
																		{16'h0C00, 16'h8C00, request.get_word(0), request.get_word(1)});
			
			fork			
				begin			
					send_crm_transmission(2'b11, {request.get_word(0), request.get_word(1)});
					#500us;
				end
				begin
					#30us;
					send_slave_response(2'b01, crm_packet1.data);
					send_slave_response(2'b10, crm_packet2.data);
				end
			join
			
			// incomplete read CRM data -> second buffer must be cleared too
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3C00, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C03, 16'h3C00, 16'h0008, crm_packet1.get_word(0)});
			// expect no more CRM data
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3C00, 16'h3000, 16'h3000, 16'h3000, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C00, 16'h3C00, 16'h0000, 16'h0000, 16'h0000, 16'h0000, 16'h0000, 16'h0000});
			
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("multiple_crms_in_one_frame_without_error_test")
			dsi3_crm_packet requests[$];
			dsi3_crm_packet response_channel_0[$];
			dsi3_crm_packet response_channel_1[$];
			
			repeat(3) begin
				requests.push_back(create_crm_packet());
				response_channel_0.push_back(create_crm_packet());
				response_channel_1.push_back(create_crm_packet());
			end
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h8C00, requests[0].get_word(0), requests[0].get_word(1), 16'h8C00, requests[1].get_word(0), requests[1].get_word(1), 16'h8C00, requests[2].get_word(0), requests[2].get_word(1), 16'h1000},
																		{16'h0C00, 16'h8C00, requests[0].get_word(0), requests[0].get_word(1), 16'h8C00, requests[1].get_word(0), requests[1].get_word(1), 16'h8C00, requests[2].get_word(0), requests[2].get_word(1)});
			#10us;
			fork			
				begin			
					send_crm_transmission(2'b11, {requests[0].get_word(0), requests[0].get_word(1)});
					#30us;
					send_slave_response(2'b01, response_channel_0[0].data);
					send_slave_response(2'b10, response_channel_1[0].data);
					#450us;
				end
				begin
					#455us;
					send_crm_transmission(2'b11, {requests[1].get_word(0), requests[1].get_word(1)});
					#30us;
					send_slave_response(2'b01, response_channel_0[1].data);
					send_slave_response(2'b10, response_channel_1[1].data);
				end
				begin
					#910us;
					send_crm_transmission(2'b11, {requests[2].get_word(0), requests[2].get_word(1)});
					#30us;
					send_slave_response(2'b01, response_channel_0[2].data);
					send_slave_response(2'b10, response_channel_1[2].data);
				end
			join
			#400us;
		
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, IDLE)
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].state, IDLE)
			
			// read CRM data channel 0
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3400, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C03, 16'h3400, 16'h0008, response_channel_0[0].get_word(0), response_channel_0[0].get_word(1)});
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3400, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C03, 16'h3400, 16'h0008, response_channel_0[1].get_word(0), response_channel_0[1].get_word(1)});
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3400, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C03, 16'h3400, 16'h0008, response_channel_0[2].get_word(0), response_channel_0[2].get_word(1)});
			
			// read CRM data channel 1
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3800, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C02, 16'h3800, 16'h0008, response_channel_1[0].get_word(0), response_channel_1[0].get_word(1)});
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3800, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C02, 16'h3800, 16'h0008, response_channel_1[1].get_word(0), response_channel_1[1].get_word(1)});
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3800, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C02, 16'h3800, 16'h0008, response_channel_1[2].get_word(0), response_channel_1[2].get_word(1)});
			
			verify_uvm_errors();
		`SVTEST_END

		//=============================================================================
		
		`SVTEST ("crm_read_data_with_additional_command_in_frame_and_error_in_second_word_test")
			dsi3_crm_packet request = create_crm_packet();
			dsi3_crm_packet crm_packet = create_crm_packet();
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h8400, request.get_word(0), request.get_word(1), 16'h1000},
																		{16'h0C00, 16'h8400, request.get_word(0), request.get_word(1)});
			fork			
				begin			
					send_crm_transmission(2'b01, {request.get_word(0), request.get_word(1)});
					#500us;
				end
				begin
					#30us;
					send_slave_response(2'b01, crm_packet.data);
				end
			join
		
			// clear PDCM buffer + read CRM data
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h7C02, 16'h3400, 16'h3000, 16'h3000, 16'h3000              , 16'h1000},
					{16'h0C01, 16'h7C02, 16'h3400, 16'h0008, crm_packet.get_word(0), 16'haffe});
						
			uvm_report_mock::expect_error("master_checker_0", $sformatf("read unexpected data in CRM at channel 0 at word 1, expected 0x%4h, read 0xaffe", crm_packet.get_word(1)));
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("crm_read_data_with_timing_errors_test")
			dsi3_crm_packet request = create_crm_packet();
			dsi3_crm_packet crm_packet1 = create_crm_packet();
			dsi3_crm_packet crm_packet2 = create_crm_packet();
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h8C00, request.get_word(0), request.get_word(1), 16'h1000},
																		{16'h0C00, 16'h8C00, request.get_word(0), request.get_word(1)});
			fork			
				begin			
					send_crm_transmission(2'b11, {request.get_word(0), request.get_word(1)});
					#500us;
				end
				begin
					#5us; // too early
					send_slave_response(2'b01, crm_packet1.data);
				end
				begin
					#70us; // too late
					send_slave_response(2'b10, crm_packet2.data);
				end
			join
		
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, IDLE)
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].state, IDLE)
			
			// read CRM data
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3400, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C03, 16'h3400, 16'h0808, crm_packet1.get_word(0), crm_packet1.get_word(1)});
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3800, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C02, 16'h3800, 16'h0808, crm_packet2.get_word(0), crm_packet2.get_word(1)});
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("crm_read_data_with_timing_errors_missing_test")
			dsi3_crm_packet request = create_crm_packet();
			dsi3_crm_packet crm_packet1 = create_crm_packet();
			dsi3_crm_packet crm_packet2 = create_crm_packet();
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h8C00, request.get_word(0), request.get_word(1), 16'h1000},
																		{16'h0C00, 16'h8C00, request.get_word(0), request.get_word(1)});
			fork			
				begin			
					send_crm_transmission(2'b11, {request.get_word(0), request.get_word(1)});
					#500us;
				end
				begin
					#70us; // too late
					send_slave_response(2'b01, crm_packet1.data);
				end
				begin
					#5us; // too early
					send_slave_response(2'b10, crm_packet2.data);
				end
			join
		
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, IDLE)
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].state, IDLE)
			
			// read CRM data
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3400, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C03, 16'h3400, 16'h0008, crm_packet1.get_word(0), crm_packet1.get_word(1)});
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3800, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C02, 16'h3800, 16'h0008, crm_packet2.get_word(0), crm_packet2.get_word(1)});
	
			uvm_report_mock::expect_error("master_checker_0", $sformatf("unexpected TE (timing error) flag in packet header at channel 0, expected 1, read 0"));
			uvm_report_mock::expect_error("master_checker_1", $sformatf("unexpected TE (timing error) flag in packet header at channel 1, expected 1, read 0"));
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("crm_read_data_after_clear_data_buffer_test")
			dsi3_crm_packet request = create_crm_packet();
			dsi3_crm_packet crm_packet1 = create_crm_packet();
			dsi3_crm_packet crm_packet2 = create_crm_packet();
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h8C00, request.get_word(0), request.get_word(1), 16'h1000},
																		{16'h0C00, 16'h8C00, request.get_word(0), request.get_word(1)});
			fork			
				begin			
					send_crm_transmission(2'b11, {request.get_word(0), request.get_word(1)});
					#500us;
				end
				begin
					#30us;
					send_slave_response(2'b01, crm_packet1.data);
					send_slave_response(2'b10, crm_packet2.data);
				end
			join
			
			// clear CRM data buffer
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h7C01, 16'h1000},
																		{16'h0C03, 16'h7C01});
			// read CRM data
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3400, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C00, 16'h3400, 16'h0000, 16'h0000, 16'h0000});
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3800, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C00, 16'h3800, 16'h0000, 16'h0000, 16'h0000});
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("crm_transmit_and_read_data_in_one_frame_test")
			dsi3_crm_packet request = create_crm_packet();
			dsi3_crm_packet crm_packet1 = create_crm_packet();
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h8400, request.get_word(0), request.get_word(1),            16'h3400, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
																		{16'h0C00, 16'h8400           , request.get_word(0), request.get_word(1), 16'h3400, 16'h0000, 16'h0000, 16'h0000});
			fork			
				begin			
					send_crm_transmission(2'b01, {request.get_word(0), request.get_word(1)});
					#500us;
				end
				begin
					#30us;
					send_slave_response(2'b01, crm_packet1.data);
				end
			join
			
			#10us;
			// read CRM data
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3400, 16'h3000, 16'h3000, 16'h3000               , 16'h1000},
					{16'h0C01, 16'h3400, 16'h0008, crm_packet1.get_word(0), crm_packet1.get_word(1)});
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("crm_read_data_without_error_only_4_symbols_test")
			dsi3_crm_packet request = create_crm_packet();
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h8400, request.get_word(0), request.get_word(1), 16'h1000},
																		{16'h0C00, 16'h8400, request.get_word(0), request.get_word(1)});
			fork			
				begin			
					send_crm_transmission(2'b01, {request.get_word(0), request.get_word(1)});
					#500us;
				end
				begin
					#30us;
					send_slave_response(2'b01, {4'ha, 4'hb, 4'hc, 4'hd});
				end
			join
		
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, IDLE)
			
			// read CRM data
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3400, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C01, 16'h3400, 16'h3004, 16'habcd, 16'h0000});
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("crm_read_data_without_error_too_many_symbols_test")
			dsi3_crm_packet request = create_crm_packet();
			dsi3_crm_packet crm_packet1 = create_crm_packet();
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h8400, request.get_word(0), request.get_word(1), 16'h1000},
																		{16'h0C00, 16'h8400, request.get_word(0), request.get_word(1)});
			fork			
				begin			
					send_crm_transmission(2'b01, {request.get_word(0), request.get_word(1)});
					#500us;
				end
				begin
					#30us;
					send_slave_response(2'b01, {4'h1, 4'h2, 4'h3, 4'h4, 4'h5, 4'h6, 4'h7, 4'h8, 4'h9}); // slave response with 9 symbols
				end
			join
		
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, IDLE)
			
			// read CRM data
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3400, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C01, 16'h3400, 16'h3009, 16'h1234, 16'h5678});
			verify_uvm_errors();
		`SVTEST_END

		//=============================================================================
		
		`SVTEST ("crm_read_data_ignore_less_than_4_symbols_test")
			dsi3_crm_packet request = create_crm_packet();
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h8400, request.get_word(0), request.get_word(1), 16'h1000},
																		{16'h0C00, 16'h8400, request.get_word(0), request.get_word(1)});
			fork			
				begin			
					send_crm_transmission(2'b01, {request.get_word(0), request.get_word(1)});
					#500us;
				end
				begin
					#30us;
					send_slave_response(2'b01, {4'ha, 4'hb, 4'hc});
				end
			join
		
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, IDLE)
			
			// read CRM data
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3400, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C01, 16'h3400, 16'h2000, 16'h0000, 16'h0000});
			verify_uvm_errors();
		`SVTEST_END

		//=============================================================================
		
		`SVTEST ("crm_read_data_ignore_less_than_4_symbols_followed_by_normal_crm_test")
			dsi3_crm_packet request = create_crm_packet();
			dsi3_crm_packet crm_packet = create_crm_packet();
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h8400, request.get_word(0), request.get_word(1), 16'h1000},
																		{16'h0C00, 16'h8400, request.get_word(0), request.get_word(1)});
			fork			
				begin			
					send_crm_transmission(2'b01, {request.get_word(0), request.get_word(1)});
					#500us;
				end
				begin
					#30us;
					send_slave_response(2'b01, {4'ha, 4'hb, 4'hc});
				end
			join
				
			// read CRM data
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3400, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C01, 16'h3400, 16'h2000, 16'h0000, 16'h0000});
			
			// new CRM request
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h8400, request.get_word(0), request.get_word(1), 16'h1000},
																		{16'h0C00, 16'h8400, request.get_word(0), request.get_word(1)});

			fork			
				begin			
					send_crm_transmission(2'b01, {request.get_word(0), request.get_word(1)});
					#500us;
				end
				begin
					#30us;
					send_slave_response(2'b01, crm_packet.data);
				end
			join
		
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, IDLE)
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].state, IDLE)
			
			// read CRM data
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3400, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C01, 16'h3400, 16'h0008, crm_packet.get_word(0), crm_packet.get_word(1)});
			
			verify_uvm_errors();
		`SVTEST_END
				
		//=============================================================================
		
		`SVTEST ("crm_no_response_read_data_test")
			dsi3_crm_packet request = create_crm_packet();
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h8C00, request.get_word(0), request.get_word(1), 16'h1000},
																		{16'h0C00, 16'h8C00, request.get_word(0), request.get_word(1)});
			send_crm_transmission(2'b11, {request.get_word(0), request.get_word(1)});
			#500us;
		
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, IDLE)
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].state, IDLE)
			
			// read CRM data -> expect no data and SCE flag
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3400, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C03, 16'h3400, 16'h2000, 16'h0000, 16'h0000});
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3800, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C02, 16'h3800, 16'h2000, 16'h0000, 16'h0000});
			verify_uvm_errors();
		`SVTEST_END

		//=============================================================================
		
		`SVTEST ("crm_no_response_followed_by_clear_data_buffer_read_data_test")
			dsi3_crm_packet request = create_crm_packet();
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h8C00, request.get_word(0), request.get_word(1), 16'h1000},
																		{16'h0C00, 16'h8C00, request.get_word(0), request.get_word(1)});
			send_crm_transmission(2'b11, {request.get_word(0), request.get_word(1)});
			#500us;

			// clear CRM data buffer
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h7C03, 16'h1000},
																		{16'h0C03, 16'h7C03});
			
			// read CRM data -> expect no data and no SCE flag
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3400, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C00, 16'h3400, 16'h0000, 16'h0000, 16'h0000});
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3800, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C00, 16'h3800, 16'h0000, 16'h0000, 16'h0000});
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("crm_no_response_and_valid_response_read_data_test")
			dsi3_crm_packet request1 = create_crm_packet();
			dsi3_crm_packet request2 = create_crm_packet();
			dsi3_crm_packet crm_packet1 = create_crm_packet();
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h8400, request1.get_word(0), request1.get_word(1), 16'h1000},
																		{16'h0C00, 16'h8400, request1.get_word(0), request1.get_word(1)});

			send_crm_transmission(2'b01, {request1.get_word(0), request1.get_word(1)});
			#500us;

			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h8400, request2.get_word(0), request2.get_word(1), 16'h1000},
																		{16'h0C01, 16'h8400, request2.get_word(0), request2.get_word(1)});
			
			fork			
				begin			
					send_crm_transmission(2'b01, {request2.get_word(0), request2.get_word(1)});
					#500us;
				end
				begin
					#20us;
					send_slave_response(2'b01, crm_packet1.data);
				end
			join
		
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, IDLE)
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].state, IDLE)
			
			// read first CRM data -> no response: expect no data and SCE flag
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3400, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C01, 16'h3400, 16'h2000, 16'h0000, 16'h0000});
			// read second CRM data -> expect valid data
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3400, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C01, 16'h3400, 16'h0008, crm_packet1.get_word(0), crm_packet1.get_word(1)});
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("crm_broadcast_no_response_read_data_test")
			dsi3_crm_packet request = create_crm_packet();
			dsi3_crm_packet crm_packet1 = create_crm_packet();
			dsi3_crm_packet crm_packet2 = create_crm_packet();
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h8C01, request.get_word(0), request.get_word(1), 16'h1000},
																		{16'h0C00, 16'h8C01, request.get_word(0), request.get_word(1)});
			fork			
				begin			
					send_crm_transmission(2'b11, {request.get_word(0), request.get_word(1)});
					#500us;
				end
				begin
					#30us;
					send_slave_response(2'b01, crm_packet1.data);
					send_slave_response(2'b10, crm_packet2.data);
				end
			join
		
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, IDLE)
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].state, IDLE)
			
			// read CRM data -> NR flag is set, expect no data
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3400, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C00, 16'h3400, 16'h0000, 16'h0000, 16'h0000});
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3800, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C00, 16'h3800, 16'h0000, 16'h0000, 16'h0000});
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("crm_broadcast_no_response_read_data_error_test")
			dsi3_crm_packet request = create_crm_packet();
			dsi3_crm_packet crm_packet1 = create_crm_packet();
			dsi3_crm_packet crm_packet2 = create_crm_packet();
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h8C01, request.get_word(0), request.get_word(1), 16'h1000},
																		{16'h0C00, 16'h8C01, request.get_word(0), request.get_word(1)});
			fork			
				begin			
					send_crm_transmission(2'b11, {request.get_word(0), request.get_word(1)});
					#500us;
				end
				begin
					#30us;
					send_slave_response(2'b01, crm_packet1.data);
					send_slave_response(2'b10, crm_packet2.data);
				end
			join
		
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, IDLE)
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].state, IDLE)
			
			// read CRM data -> NR flag is set, expect no data
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3400, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C00, 16'h3400, 16'h0008, crm_packet1.get_word(0), crm_packet1.get_word(1)});
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3800, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C00, 16'h3800, 16'h0008, crm_packet2.get_word(0), crm_packet2.get_word(1)});
	
			uvm_report_mock::expect_error("master_checker_0", $sformatf("unexpected symbol count in read CRM at channel 0, expected 0, read 8 symbols"));
			uvm_report_mock::expect_error("master_checker_0", $sformatf("read unexpected data in CRM at channel 0 at word 0, expected 0x0000, read 0x%4h", crm_packet1.get_word(0)));
			uvm_report_mock::expect_error("master_checker_0", $sformatf("read unexpected data in CRM at channel 0 at word 1, expected 0x0000, read 0x%4h", crm_packet1.get_word(1)));
			uvm_report_mock::expect_error("master_checker_1", $sformatf("unexpected symbol count in read CRM at channel 1, expected 0, read 8 symbols"));
			uvm_report_mock::expect_error("master_checker_1", $sformatf("read unexpected data in CRM at channel 1 at word 0, expected 0x0000, read 0x%4h", crm_packet2.get_word(0)));
			uvm_report_mock::expect_error("master_checker_1", $sformatf("read unexpected data in CRM at channel 1 at word 1, expected 0x0000, read 0x%4h", crm_packet2.get_word(1)));
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("multiple_crm_read_data_without_error_test")
			dsi3_crm_packet request = create_crm_packet();
			dsi3_crm_packet crm_packet1 = create_crm_packet();
			dsi3_crm_packet crm_packet2 = create_crm_packet();
		
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h8800, request.get_word(0), request.get_word(1), 16'h1000},
																		{16'h0C00, 16'h8800, request.get_word(0), request.get_word(1)});
			fork			
				begin			
					send_crm_transmission(2'b10, {request.get_word(0), request.get_word(1)});
					#500us;
				end
				begin
					#30us;
					send_slave_response(2'b10, crm_packet1.data);
				end
			join
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h8800, request.get_word(0), request.get_word(1), 16'h1000},
																		{16'h0C02, 16'h8800, request.get_word(0), request.get_word(1)});
			fork			
				begin			
					send_crm_transmission(2'b10, {request.get_word(0), request.get_word(1)});
					#500us;
				end
				begin
					#30us;
					send_slave_response(2'b10, crm_packet2.data);
				end
			join
			
			// clear PDCM buffer must not have any effect
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h7C02, 16'h1000},
																		{16'h0C02, 16'h7C02});
			
			// read CRM data
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3800, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C02, 16'h3800, 16'h0008, crm_packet1.get_word(0), crm_packet1.get_word(1)});
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3800, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C02, 16'h3800, 16'h0008, crm_packet2.get_word(0), crm_packet2.get_word(1)});
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("crm_read_unexpected_data_test")
			dsi3_crm_packet request = create_crm_packet();
			dsi3_crm_packet crm_packet = create_crm_packet();
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h8400, request.get_word(0), request.get_word(1), 16'h1000},
																		{16'h0C00, 16'h8400, request.get_word(0), request.get_word(1)});
			fork			
				begin			
					send_crm_transmission(2'b01, {request.get_word(0), request.get_word(1)});
					#500us;
				end
				begin
					#30us;
					send_slave_response(2'b01, crm_packet.data);
				end
			join
		
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, IDLE)
			
			// read CRM data
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3400, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C01, 16'h3400, 16'h0008, 16'h1AA1, crm_packet.get_word(1)});
		
			uvm_report_mock::expect_error("master_checker_0", $sformatf("read unexpected data in CRM at channel 0 at word 0, expected 0x%4h, read 0x1aa1", crm_packet.get_word(0)));
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("crm_read_data_crc_error_test")
			dsi3_crm_packet request = create_crm_packet();
			dsi3_crm_packet crm_packet1 = create_crm_packet(1'b0);
			dsi3_crm_packet crm_packet2 = create_crm_packet(1'b0);
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h8C00, request.get_word(0), request.get_word(1), 16'h1000},
																		{16'h0C00, 16'h8C00, request.get_word(0), request.get_word(1)});
			fork			
				begin			
					send_crm_transmission(2'b11, {request.get_word(0), request.get_word(1)});
					#500us;
				end
				begin
					#30us;
					send_slave_response(2'b01, crm_packet1.data);
					send_slave_response(2'b10, crm_packet2.data);
				end
			join
		
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, IDLE)
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].state, IDLE)
			
			// read CRM data
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3400, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C03, 16'h3400, 16'h0008, crm_packet1.get_word(0), crm_packet1.get_word(1)});
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3800, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C02, 16'h3800, 16'h0008, crm_packet2.get_word(0), crm_packet2.get_word(1)});
			
			uvm_report_mock::expect_error("master_checker_0", "unexpected CRC flag in packet header at channel 0, expected 1, read 0");
			uvm_report_mock::expect_error("master_checker_1", "unexpected CRC flag in packet header at channel 1, expected 1, read 0");
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("crm_read_data_crc_error_crc_disabled_test")
			m_top_config.m_master_transmission_checker[0].configuration_subscriber.crc_en = 0;
			m_top_config.m_master_transmission_checker[1].configuration_subscriber.crc_en = 0;
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h8C00, 16'h1234, 16'h4321, 16'h1000},
																		{16'h0C00, 16'h8C00, 16'h1234, 16'h4321});
			fork			
				begin			
					send_crm_transmission(2'b11, {16'h1234, 16'h4321});
					#500us;
				end
				begin
					#30us;
					send_slave_response_words(2'b01, {16'haffe, 16'hdead});
					send_slave_response_words(2'b10, {16'hbeef, 16'hc0de});
				end
			join
		
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, IDLE)
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].state, IDLE)
			
			// read CRM data
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3400, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C03, 16'h3400, 16'h0008, 16'haffe, 16'hdead});
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3800, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C02, 16'h3800, 16'h0008, 16'hbeef, 16'hc0de});
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("crm_read_data_sce_error_test")
			dsi3_crm_packet request = create_crm_packet();
			dsi3_crm_packet crm_packet1 = create_crm_packet(1'b0);
			dsi3_crm_packet crm_packet2 = create_crm_packet(1'b0);
			// add some more symbols
			crm_packet1.data.push_back(4'hf);
			crm_packet2.data.push_back(4'h1);
			crm_packet2.data.push_back(4'h2);
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h8C00, request.get_word(0), request.get_word(1), 16'h1000},
																		{16'h0C00, 16'h8C00, request.get_word(0), request.get_word(1)});
			fork			
				begin			
					send_crm_transmission(2'b11, {request.get_word(0), request.get_word(1)});
					#500us;
				end
				begin
					#30us;
					send_slave_response(2'b01, crm_packet1.data);
					send_slave_response(2'b10, crm_packet2.data);
				end
			join
		
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, IDLE)
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].state, IDLE)
			
			// read CRM data
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3400, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C03, 16'h3400, 16'h0009, crm_packet1.get_word(0), crm_packet1.get_word(1)});
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3800, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C02, 16'h3800, 16'h000a, crm_packet2.get_word(0), crm_packet2.get_word(1)});
			
			uvm_report_mock::expect_error("master_checker_0", "unexpected SCE (symbol count error) flag in packet header at channel 0, expected 1, read 0");
			uvm_report_mock::expect_error("master_checker_0", "unexpected CRC flag in packet header at channel 0, expected 1, read 0");
			uvm_report_mock::expect_error("master_checker_1", "unexpected SCE (symbol count error) flag in packet header at channel 1, expected 1, read 0");
			uvm_report_mock::expect_error("master_checker_1", "unexpected CRC flag in packet header at channel 1, expected 1, read 0");
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("crm_read_unexpected_symbol_count_and_data_test")
			dsi3_crm_packet request = create_crm_packet();
			dsi3_crm_packet crm_packet = create_crm_packet();
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h8800, request.get_word(0), request.get_word(1), 16'h1000},
																		{16'h0C00, 16'h8800, request.get_word(0), request.get_word(1)});
			fork			
				begin			
					send_crm_transmission(2'b10, {request.get_word(0), request.get_word(1)});
					#500us;
				end
				begin
					#30us;
					send_slave_response(2'b10, crm_packet.data);
				end
			join
		
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, IDLE)
			
			// read CRM data
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3800, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C02, 16'h3800, 16'h0007, crm_packet.get_word(0), 16'h2bb2});
		
			uvm_report_mock::expect_error("master_checker_1", "unexpected symbol count in read CRM at channel 1, expected 8, read 7 symbols");
			uvm_report_mock::expect_error("master_checker_1", $sformatf("read unexpected data in CRM at channel 1 at word 1, expected 0x%4h, read 0x2bb2", crm_packet.get_word(1)));
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("crm_read_data_without_previous_slave_answer_test")
			// read CRM data
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3400, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C00, 16'h3400, 16'h0008, 16'h1001, 16'h2002});
		
			uvm_report_mock::expect_error("master_checker_0", "unexpected symbol count in read CRM at channel 0, expected 0, read 8 symbols");
			uvm_report_mock::expect_error("master_checker_0", "read unexpected data in CRM at channel 0 at word 0, expected 0x0000, read 0x1001");
			uvm_report_mock::expect_error("master_checker_0", "read unexpected data in CRM at channel 0 at word 1, expected 0x0000, read 0x2002");
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("crm_with_too_low_CRM_TIME_value_and_no_answers_test")
			dsi3_crm_packet request = create_crm_packet();
			
			m_top_config.m_master_transmission_checker[0].configuration_subscriber.crm_time = 50;
			m_top_config.m_master_transmission_checker[1].configuration_subscriber.crm_time = 50;
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h8C00, request.get_word(0), request.get_word(1), 16'h1000},
																		{16'h0C00, 16'h8C00, request.get_word(0), request.get_word(1)});
			
			send_crm_transmission(2'b11, {request.get_word(0), request.get_word(1)});
			#500us;
		
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, IDLE)
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].state, IDLE)
			
			// read CRM data
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3400, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C03, 16'h3400, 16'h2000, 16'h0000, 16'h0000});
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3800, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C02, 16'h3800, 16'h2000, 16'h0000, 16'h0000});
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("crm_change_CRM_TIME_during_transmission_no_error_test")
			dsi3_crm_packet request = create_crm_packet();
			dsi3_crm_packet crm_packet1 = create_crm_packet();
			dsi3_crm_packet crm_packet2 = create_crm_packet();
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h8C00, request.get_word(0), request.get_word(1), 16'h1000},
																		{16'h0C00, 16'h8C00, request.get_word(0), request.get_word(1)});
			
			fork			
				begin			
					send_crm_transmission(2'b11, {request.get_word(0), request.get_word(1)});
					#500us;
				end
				begin
					#100us;				
					m_top_config.m_master_transmission_checker[0].configuration_subscriber.crm_time = 50;
					m_top_config.m_master_transmission_checker[1].configuration_subscriber.crm_time = 50;
				end
				begin
					#30us;
					send_slave_response(2'b01, crm_packet1.data);
					send_slave_response(2'b10, crm_packet2.data);
				end
			join
		
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, IDLE)
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].state, IDLE)
			
			// read CRM data
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3400, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C03, 16'h3400, 16'h0008, crm_packet1.get_word(0), crm_packet1.get_word(1)});
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3800, 16'h3000, 16'h3000, 16'h3000, 16'h1000},
					{16'h0C02, 16'h3800, 16'h0008, crm_packet2.get_word(0), crm_packet2.get_word(1)});
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("pdcm_without_error_test")
			set_tdma_scheme(2'b11, 300, {8}, {30}, {70});
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'hCC03, 16'h1000},
																		{16'h0000, 16'hCC03});
			fork			
				begin			
					repeat(3) begin
						send_pdcm_pulse(2'b11);
						#300us;
					end
				end
				begin
					#100us;
					`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, PDCM)
					`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].period_index, 2)
					`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].state, PDCM)
					`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].period_index, 2)
					#300us;
					`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, PDCM)
					`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].period_index, 1)
					`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].state, PDCM)
					`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].period_index, 1)
					#300us;
					`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, PDCM)
					`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].period_index, 0)
					`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].state, PDCM)
					`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].period_index, 0)
					#300us;
					`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, IDLE)
					`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].state, IDLE)
				end
			join
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("pdcm_read_frame_without_valid_tdma_scheme_test")
		
			set_tdma_scheme(2'b00, 1000, {}, {}, {});
		
			// read PDCM frame
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 16'h1000},
					{16'h0C00, 16'h4400, 16'h0005});
		
			uvm_report_mock::expect_error("master_checker_0", "unexpected packet count in frame header for read without valid TDMA scheme at channel 0, expected 0, got 5 packets");
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================

		`SVTEST ("pdcm_read_frame_without_previous_slave_answer_test")
		
			set_tdma_scheme(2'b11, 300, {8, 8}, {30, 152}, {70, 192});
		
			// read PDCM frame
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
					{16'h0000, 16'h4400, 16'h0001, 16'h0008, 16'h1111, 16'h2222, 16'h0008, 16'h3333, 16'h4444});

			uvm_report_mock::expect_error("master_checker_0", "unexpected packet count in frame header for read at channel 0, expected 0, got 1 packets");
			uvm_report_mock::expect_error("master_checker_0", "unexpected symbol count in packet 0 at channel 0, expected 0, got 8");
			uvm_report_mock::expect_error("master_checker_0", "unexpected data in packet 0 at index 0 at channel 0, expected 0x0000, got 0x1111");
			uvm_report_mock::expect_error("master_checker_0", "unexpected data in packet 0 at index 1 at channel 0, expected 0x0000, got 0x2222");
			uvm_report_mock::expect_error("master_checker_0", "unexpected symbol count in packet 1 at channel 0, expected 0, got 8");
			uvm_report_mock::expect_error("master_checker_0", "unexpected data in packet 1 at index 0 at channel 0, expected 0x0000, got 0x3333");
			uvm_report_mock::expect_error("master_checker_0", "unexpected data in packet 1 at index 1 at channel 0, expected 0x0000, got 0x4444");
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================

		`SVTEST ("pdcm_read_frame_without_previous_slave_answer_no_error_test")
		
			set_tdma_scheme(2'b11, 300, {8, 8}, {30, 152}, {70, 192});
		
			// read PDCM frame
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
					{16'h0000, 16'h4400, 16'h0000, 16'h0000, 16'h0000, 16'h0000, 16'h0000, 16'h0000, 16'h0000});
		
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================

		`SVTEST ("pdcm_read_without_errors_test")
			dsi3_pdcm_packet packet1 = create_pdcm_packet(8, dsi3_pkg::SID_8Bit);
			dsi3_pdcm_packet packet2 = create_pdcm_packet(8, dsi3_pkg::SID_8Bit);
			dsi3_pdcm_packet packet3 = create_pdcm_packet(8, dsi3_pkg::SID_8Bit);
			
			set_tdma_scheme(2'b01, 300, {8}, {30}, {70});
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'hC403, 16'h1000},
																		{16'h0800, 16'hC403});
			fork			
				begin			
					repeat(3) begin
						send_pdcm_pulse(2'b01);
						#300us;
					end
				end
				begin
					#50us;
					send_slave_response(2'b01, packet1.data);
				end
				begin
					#300us;
					#50us;
					send_slave_response(2'b01, packet2.data);
				end
				begin
					#300us;
					#300us;
					#50us;
					send_slave_response(2'b01, packet3.data);
				end
			join
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
					{16'h0804, 16'h4400, 16'h0001, 16'h0008, packet1.get_word(0), packet1.get_word(1)});
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
					{16'h0804, 16'h4400, 16'h0001, 16'h0008, packet2.get_word(0), packet2.get_word(1)});
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
					{16'h0804, 16'h4400, 16'h0001, 16'h0008, packet3.get_word(0), packet3.get_word(1)});
			
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================

		`SVTEST ("pdcm_read_after_clear_buffer_test")
			dsi3_pdcm_packet packet1 = create_pdcm_packet(8, dsi3_pkg::SID_8Bit);
			dsi3_pdcm_packet packet2 = create_pdcm_packet(8, dsi3_pkg::SID_8Bit);
			dsi3_pdcm_packet packet3 = create_pdcm_packet(8, dsi3_pkg::SID_8Bit);
			
			set_tdma_scheme(2'b01, 300, {8}, {30}, {70});
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'hC403, 16'h1000},
																		{16'h0800, 16'hC403});
			fork			
				begin			
					repeat(3) begin
						send_pdcm_pulse(2'b01);
						#300us;
					end
				end
				begin
					#50us;
					send_slave_response(2'b01, packet1.data);
				end
				begin
					#300us;
					#50us;
					send_slave_response(2'b01, packet2.data);
				end
				begin
					#300us;
					#300us;
					#50us;					
					send_slave_response(2'b01, packet3.data);
				end
			join
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h7C02, 16'h1000},
																		{16'h0804, 16'h7C02});
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
					{16'h0800, 16'h4400, 16'h0000, 16'h0000, 16'h0000, 16'h0000});
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
					{16'h0800, 16'h4400, 16'h0000, 16'h0000, 16'h0000, 16'h0000});
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
					{16'h0800, 16'h4400, 16'h0000, 16'h0000, 16'h0000, 16'h0000});
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================

		`SVTEST ("pdcm_multi_packet_read_without_errors_test")
			dsi3_pdcm_packet packet1 = create_pdcm_packet(8, dsi3_pkg::SID_8Bit);
			dsi3_pdcm_packet packet2 = create_pdcm_packet(8, dsi3_pkg::SID_8Bit);
			set_tdma_scheme(2'b01, 1000, {8, 8}, {30, 152}, {70, 192});
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'hC401, 16'h1000},
																		{16'h0800, 16'hC401});
			fork			
				begin			
					send_pdcm_pulse(2'b01);
					#1100us;
				end
				begin
					#50us;
					send_slave_response(2'b01, packet1.data);
				end
				begin
					#172us;
					send_slave_response(2'b01, packet2.data);
				end
			join
			
			// clear CRM buffer must not have any effect
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h7C01, 16'h1000},
																		{16'h0804, 16'h7C01});
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
					{16'h0804, 16'h4400, 16'h0002, 16'h0008, packet1.get_word(0), packet1.get_word(1), 16'h0008, packet2.get_word(0), packet2.get_word(1)});
			verify_uvm_errors();
		`SVTEST_END

		//=============================================================================

		`SVTEST ("pdcm_multi_packet_read_with_crc_error_test")
			dsi3_pdcm_packet packet1 = create_pdcm_packet(8, dsi3_pkg::SID_8Bit, 1'b0);
			dsi3_pdcm_packet packet2 = create_pdcm_packet(8, dsi3_pkg::SID_8Bit, 1'b0);
			set_tdma_scheme(2'b01, 1000, {8, 8}, {30, 152}, {70, 192});
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'hC401, 16'h1000},
																		{16'h0800, 16'hC401});
			fork			
				begin			
					send_pdcm_pulse(2'b01);
					#1100us;
				end
				begin
					#50us;
					send_slave_response(2'b01, packet1.data);
				end
				begin
					#172us;
					send_slave_response(2'b01, packet2.data);
				end
			join
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
					{16'h0804, 16'h4400, 16'h0002, 16'h0008, packet1.get_word(0), packet1.get_word(1), 16'h0008, packet2.get_word(0), packet2.get_word(1)});
	
			uvm_report_mock::expect_error("master_checker_0", "unexpected CRC flag in packet header of packet index 0 at channel 0, expected 1, read 0");
			uvm_report_mock::expect_error("master_checker_0", "unexpected CRC flag in packet header of packet index 1 at channel 0, expected 1, read 0");
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================

		`SVTEST ("pdcm_ignore_packets_not_defined_in_tdma_scheme_test")
			dsi3_pdcm_packet packet = create_pdcm_packet(8, dsi3_pkg::SID_8Bit);
			set_tdma_scheme(2'b01, 1000, {8}, {30}, {70});
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'hC401, 16'h1000},
																		{16'h0800, 16'hC401});
			fork			
				begin			
					send_pdcm_pulse(2'b01);
					#1100us;
				end
				begin
					#50us;
					send_slave_response(2'b01, packet.data);
				end
				begin
					#300us;
					send_slave_response_words(2'b01, {16'h3333, 16'h4444});
				end
			join
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
					{16'h0804, 16'h4400, 16'h8002, 16'h0008, packet.get_word(0), packet.get_word(1)});
			
			// expect no more data
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
					{16'h0800, 16'h4400, 16'h0000, 16'h0000, 16'h0000, 16'h0000});
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================

		`SVTEST ("pdcm_ignore_packets_not_defined_in_tdma_scheme_error_test")
			dsi3_pdcm_packet packet = create_pdcm_packet(8, dsi3_pkg::SID_8Bit);
			set_tdma_scheme(2'b01, 1000, {8}, {30}, {70});
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'hC401, 16'h1000},
																		{16'h0800, 16'hC401});
			fork			
				begin			
					send_pdcm_pulse(2'b01);
					#1100us;
				end
				begin
					#50us;
					send_slave_response(2'b01, packet.data);
				end
				begin
					#300us;
					send_slave_response_words(2'b01, {16'h3333, 16'h4444});
				end
			join
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
					{16'h0804, 16'h4400, 
						16'h0002, 
							16'h0008, packet.get_word(0), packet.get_word(1)});
			
			uvm_report_mock::expect_error("master_checker_0", "unexpected PC flag value in frame header for read at channel 0, expected 1, got 0");
			verify_uvm_errors();
		`SVTEST_END
	
		//=============================================================================

		`SVTEST ("pdcm_multi_packet_read_packet_count_error_test")
			dsi3_pdcm_packet packet1 = create_pdcm_packet(8, dsi3_pkg::SID_8Bit);
			dsi3_pdcm_packet packet2 = create_pdcm_packet(8, dsi3_pkg::SID_8Bit);			
			set_tdma_scheme(2'b01, 1000, {8, 8}, {30, 152}, {70, 192});
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'hC401, 16'h1000},
																		{16'h0800, 16'hC401});
			fork			
				begin			
					send_pdcm_pulse(2'b01);
					#1100us;
				end
				begin
					#50us;
					send_slave_response(2'b01, packet1.data);
				end
				begin
					#172us;
					send_slave_response(2'b01, packet2.data);
				end
			join
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
					{16'h0804, 16'h4400, 
						16'h0001, 
							16'h0008, packet1.get_word(0), packet1.get_word(1), 
							16'h0008, packet2.get_word(0), packet2.get_word(1)});
	
			uvm_report_mock::expect_error("master_checker_0", "unexpected packet count in frame header for read at channel 0, expected 2, got 1 packets");
			verify_uvm_errors();
		`SVTEST_END
	
		//=============================================================================
		
		`SVTEST ("pdcm_multi_packet_read_symbol_count_error_test")
			dsi3_pdcm_packet packets[$];
			repeat(4) packets.push_back(create_pdcm_packet(8, dsi3_pkg::SID_8Bit));
			set_tdma_scheme(2'b11, 1000, {8, 8}, {30, 152}, {70, 192});
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'hCC01, 16'h1000},
																		{16'h0000, 16'hCC01});
			fork			
				begin			
					send_pdcm_pulse(2'b11);
					#1100us;
				end
				begin
					#50us;
					send_slave_response(2'b01, packets[0].data);
					send_slave_response(2'b10, packets[1].data);
				end
				begin
					#172us;
					send_slave_response(2'b01, packets[2].data);
					send_slave_response(2'b10, packets[3].data);
				end
			join
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4C00, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
					{16'h000C, 16'h4C00, 
						16'h0002, 
							16'h0008, packets[0].get_word(0), packets[0].get_word(1), 
							16'h0008, packets[2].get_word(0), packets[2].get_word(1), 
						16'h0002, 
							16'h0008, packets[1].get_word(0), packets[1].get_word(1), 
							16'h0007, packets[3].get_word(0), packets[3].get_word(1)});
	
			uvm_report_mock::expect_error("master_checker_1", "unexpected symbol count in packet 1 at channel 1, expected 8, got 7");
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("pdcm_multi_packet_read_wrong_data_error_test")
			dsi3_pdcm_packet packets[$];
			repeat(4) packets.push_back(create_pdcm_packet(8, dsi3_pkg::SID_8Bit));	
			set_tdma_scheme(2'b11, 1000, {8, 8}, {30, 152}, {70, 192});
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'hCC01, 16'h1000},
																		{16'h0000, 16'hCC01});
			fork			
				begin			
					send_pdcm_pulse(2'b11);
					#1100us;
				end
				begin
					#50us;
					send_slave_response(2'b01, packets[0].data);
					send_slave_response(2'b10, packets[1].data);
				end
				begin
					#172us;
					send_slave_response(2'b01, packets[2].data);
					send_slave_response(2'b10, packets[3].data);
				end
			join
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4C00, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
					{16'h000C, 16'h4C00, 
						16'h0002, 
							16'h0008, 16'h1000, packets[0].get_word(1), 
							16'h0008, packets[2].get_word(0), 16'h4000, 
						16'h0002, 
							16'h0008, 16'haaa0, 16'h0bbb, 
							16'h0008, packets[3].get_word(0), packets[3].get_word(1)});
	
			uvm_report_mock::expect_error("master_checker_0", $sformatf("unexpected data in packet 0 at index 0 at channel 0, expected 0x%4h, got 0x1000", packets[0].get_word(0)));
			uvm_report_mock::expect_error("master_checker_0", $sformatf("unexpected data in packet 1 at index 1 at channel 0, expected 0x%4h, got 0x4000", packets[2].get_word(1)));
			uvm_report_mock::expect_error("master_checker_1", $sformatf("unexpected data in packet 0 at index 0 at channel 1, expected 0x%4h, got 0xaaa0", packets[1].get_word(0)));
			uvm_report_mock::expect_error("master_checker_1", $sformatf("unexpected data in packet 0 at index 1 at channel 1, expected 0x%4h, got 0x0bbb", packets[1].get_word(1)));
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================

		`SVTEST ("pdcm_multi_packet_read_first_and_last_packet_timing_error_test")
			dsi3_pdcm_packet packet1 = create_pdcm_packet(8, dsi3_pkg::SID_8Bit);
			dsi3_pdcm_packet packet2 = create_pdcm_packet(8, dsi3_pkg::SID_8Bit);
			set_tdma_scheme(2'b01, 1000, {8, 8}, {30, 152}, {70, 192});
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'hC401, 16'h1000},
																		{16'h0800, 16'hC401});
			fork			
				begin			
					send_pdcm_pulse(2'b01);
					#1100us;
				end
				begin
					#20us; // too early
					send_slave_response(2'b01, packet1.data);
				end
				begin
					#500us; // much too late
					send_slave_response(2'b01, packet2.data);
				end
			join
			
			#10us;
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
					{16'h0804, 16'h4400, 
						16'h0002, 
							16'h0808, packet1.get_word(0), packet1.get_word(1), 
							16'h0808, packet2.get_word(0), packet2.get_word(1)});
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================

		`SVTEST ("pdcm_packet_at_period_end_timing_error_test")
			dsi3_pdcm_packet packet1 = create_pdcm_packet(8, dsi3_pkg::SID_8Bit);
			dsi3_pdcm_packet packet2 = create_pdcm_packet(8, dsi3_pkg::SID_8Bit);
			set_tdma_scheme(2'b01, 250, {8, 8}, {30, 150}, {70, 190});
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'hC401, 16'h1000},
																		{16'h0800, 16'hC401});
			fork			
				begin			
					send_pdcm_pulse(2'b01);
					#1100us;
				end
				begin
					#50us; 
					send_slave_response(2'b01, packet1.data);
				end
				begin
					#170us;
					send_slave_response(2'b01, packet2.data); // -> TE because of too small PDCM period
				end
			join
			
			#10us;
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
					{16'h0804, 16'h4400, 
						16'h0002, 
							16'h0008, packet1.get_word(0), packet1.get_word(1), 
							16'h0008, packet2.get_word(0), packet2.get_word(1)});
			
			uvm_report_mock::expect_error("master_checker_0", "unexpected TE (timing error) flag in packet header of packet index 1 at channel 0, expected 1, read 0");
			
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================

		`SVTEST ("pdcm_multi_packet_read_timing_error_test")
			dsi3_pdcm_packet packets[$];
			repeat(4) packets.push_back(create_pdcm_packet(8, dsi3_pkg::SID_8Bit));	
			set_tdma_scheme(2'b01, 1000, {8, 8, 8, 8}, {30, 152, 274, 396}, {70, 192, 314, 436});
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'hC401, 16'h1000},
																		{16'h0800, 16'hC401});
			fork			
				begin			
					send_pdcm_pulse(2'b01);
					#1100us;
				end
				begin
					#50us; // in time
					send_slave_response(2'b01, packets[0].data);
				end
				begin
					#140us; // too early
					send_slave_response(2'b01, packets[1].data);
				end
				begin
					#320us; // too late
					send_slave_response(2'b01, packets[2].data);
				end
				begin
					#416us; // in time
					send_slave_response(2'b01, packets[3].data);
				end
			join
			
			#10us;
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
					{16'h0804, 16'h4400, 
						16'h0004, 
							16'h0008, packets[0].get_word(0), packets[0].get_word(1), 
							16'h0808, packets[1].get_word(0), packets[1].get_word(1),
							16'h0808, packets[2].get_word(0), packets[2].get_word(1),
							16'h0008, packets[3].get_word(0), packets[3].get_word(1)});
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("pdcm_denso_tdma_scheme_without_error_test")
			dsi3_pdcm_packet packets[$]; 
			tdma_scheme_pdcm_denso denso_scheme = new();
			denso_scheme.valid = 1'b1;
			tdma_scheme_upload_listener::schemes[0] = denso_scheme;
			
			repeat(7) packets.push_back(create_pdcm_packet(8, dsi3_pkg::SID_8Bit));	
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'hC401, 16'h1000},
																		{16'h0800, 16'hC401});
			fork			
				begin			
					send_pdcm_pulse(2'b01);
					#1100us;
				end
				begin
					#50us;
					foreach(packets[i]) begin
						send_slave_response(2'b01, packets[i].data);
						#135us;
					end
				end
			join
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
					{16'h0804, 16'h4400, 
						16'h0007, 
							16'h0008, packets[0].get_word(0), packets[0].get_word(1),
							16'h0008, packets[1].get_word(0), packets[1].get_word(1),
							16'h0008, packets[2].get_word(0), packets[2].get_word(1),
							16'h0008, packets[3].get_word(0), packets[3].get_word(1),
							16'h0008, packets[4].get_word(0), packets[4].get_word(1),
							16'h0008, packets[5].get_word(0), packets[5].get_word(1),
							16'h0008, packets[6].get_word(0), packets[6].get_word(1)});
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================

		`SVTEST ("pdcm_missing_packet_read_without_errors_test")
			dsi3_pdcm_packet packet2 = create_pdcm_packet(8, dsi3_pkg::SID_8Bit);
			set_tdma_scheme(2'b01, 1000, {8, 8}, {30, 152}, {70, 192});
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'hC401, 16'h1000},
																		{16'h0800, 16'hC401});
			fork			
				begin			
					send_pdcm_pulse(2'b01);
					#1100us;
				end
				// send second packet only
				begin
					#172us;
					send_slave_response(2'b01, packet2.data);
				end
			join
			
			// clear CRM buffer must not have any effect
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h7C01, 16'h1000},
																		{16'h0804, 16'h7C01});
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
					{16'h0804, 16'h4400, 16'h0001, 16'h2000, 16'h0000, 16'h0000, 16'h0008, packet2.get_word(0), packet2.get_word(1)});
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("pdcm_denso_tdma_scheme_missing_responses_without_error_test")
			dsi3_pdcm_packet packets[$]; 
			tdma_scheme_pdcm_denso denso_scheme = new();
			denso_scheme.valid = 1'b1;
			tdma_scheme_upload_listener::schemes[0] = denso_scheme;
			
			repeat(7) packets.push_back(create_pdcm_packet(8, dsi3_pkg::SID_8Bit));	
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'hC401, 16'h1000},
																		{16'h0800, 16'hC401});
			fork			
				begin			
					send_pdcm_pulse(2'b01);
					#1100us;
				end
				begin
					#50us;
					foreach(packets[i]) begin
						if(i % 2 == 0) send_slave_response(2'b01, packets[i].data);
						#135us;
					end
				end
			join
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
					{16'h0804, 16'h4400, 
						16'h0004, 
							16'h0008, packets[0].get_word(0), packets[0].get_word(1),
							16'h2000, 16'h0000, 16'h0000,
							16'h0008, packets[2].get_word(0), packets[2].get_word(1),
							16'h2000, 16'h0000, 16'h0000,
							16'h0008, packets[4].get_word(0), packets[4].get_word(1),
							16'h2000, 16'h0000, 16'h0000,
							16'h0008, packets[6].get_word(0), packets[6].get_word(1)});
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("pdcm_denso_tdma_scheme_all_packets_missing_without_error_test")
		
			set_tdma_scheme(2'b01, 1000, {16, 16, 16, 16}, {50, 250, 450, 650}, {60, 260, 460, 660});
			tdma_scheme_upload_listener::schemes[0].packets[0].id_symbol_count = dsi3_pkg::SID_0Bit;
			tdma_scheme_upload_listener::schemes[0].packets[1].id_symbol_count = dsi3_pkg::SID_4Bit;
			tdma_scheme_upload_listener::schemes[0].packets[2].id_symbol_count = dsi3_pkg::SID_8Bit;
			tdma_scheme_upload_listener::schemes[0].packets[3].id_symbol_count = dsi3_pkg::SID_16Bit_CRC;
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'hC401, 16'h1000},
																		{16'h0800, 16'hC401});
						
			send_pdcm_pulse(2'b01);
			#1100us;
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 
						16'h4000, 
							16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 
							16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 
							16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 
							16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
					{16'h0804, 16'h4400, 
						16'h0000, 
							16'h2000, 16'h0000, 16'h0000, 16'h0000, 16'h0000,
							16'h2000, 16'h0000, 16'h0000, 16'h0000, 16'h0000,
							16'h2000, 16'h0000, 16'h0000, 16'h0000, 16'h0000,
							16'h2000, 16'h0000, 16'h0000, 16'h0000, 16'h0000});
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("pdcm_none_denso_tdma_scheme_all_packets_missing_without_error_test")
			tdma_scheme_pdcm_denso denso_scheme = new();
			denso_scheme.valid = 1'b1;
			tdma_scheme_upload_listener::schemes[0] = denso_scheme;
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'hC401, 16'h1000},
																		{16'h0800, 16'hC401});
						
			send_pdcm_pulse(2'b01);
			#1100us;
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 
						16'h4000, 
							16'h4000, 16'h4000, 16'h4000, 
							16'h4000, 16'h4000, 16'h4000, 
							16'h4000, 16'h4000, 16'h4000, 
							16'h4000, 16'h4000, 16'h4000, 
							16'h4000, 16'h4000, 16'h4000, 
							16'h4000, 16'h4000, 16'h4000, 
							16'h4000, 16'h4000, 16'h1000},
					{16'h0804, 16'h4400, 
						16'h0000, 
							16'h2000, 16'h0000, 16'h0000,
							16'h2000, 16'h0000, 16'h0000,
							16'h2000, 16'h0000, 16'h0000,
							16'h2000, 16'h0000, 16'h0000,
							16'h2000, 16'h0000, 16'h0000,
							16'h2000, 16'h0000, 16'h0000,
							16'h2000, 16'h0000, 16'h0000});
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("pdcm_denso_tdma_scheme_all_packets_missing_error_test")
			tdma_scheme_pdcm_denso denso_scheme = new();
			denso_scheme.valid = 1'b1;
			tdma_scheme_upload_listener::schemes[0] = denso_scheme;
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'hC401, 16'h1000},
																		{16'h0800, 16'hC401});
						
			send_pdcm_pulse(2'b01);
			#1100us;
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
					{16'h0804, 16'h4400, 
						16'h0000, 
							16'h0008, 16'haffe, 16'hdead,
							16'h0000, 16'h0000, 16'h0000,
							16'h0000, 16'h0000, 16'h0000,
							16'h0000, 16'h0000, 16'h0000,
							16'h0000, 16'h0000, 16'h0000,
							16'h0000, 16'h0000, 16'h0000,
							16'h0000, 16'h0000, 16'h0000});
			
			uvm_report_mock::expect_error("master_checker_0", "unexpected SCE (symbol count error) flag in packet header of packet index 0 at channel 0, expected 1, read 0");
			uvm_report_mock::expect_error("master_checker_0", "unexpected symbol count in packet 0 at channel 0, expected 0, got 8");
			uvm_report_mock::expect_error("master_checker_0", "unexpected data in packet 0 at index 0 at channel 0, expected 0x0000, got 0xaffe");
			uvm_report_mock::expect_error("master_checker_0", "unexpected data in packet 0 at index 1 at channel 0, expected 0x0000, got 0xdead");
			uvm_report_mock::expect_error("master_checker_0", "unexpected SCE (symbol count error) flag in packet header of packet index 1 at channel 0, expected 1, read 0");
			uvm_report_mock::expect_error("master_checker_0", "unexpected SCE (symbol count error) flag in packet header of packet index 2 at channel 0, expected 1, read 0");
			uvm_report_mock::expect_error("master_checker_0", "unexpected SCE (symbol count error) flag in packet header of packet index 3 at channel 0, expected 1, read 0");
			uvm_report_mock::expect_error("master_checker_0", "unexpected SCE (symbol count error) flag in packet header of packet index 4 at channel 0, expected 1, read 0");
			uvm_report_mock::expect_error("master_checker_0", "unexpected SCE (symbol count error) flag in packet header of packet index 5 at channel 0, expected 1, read 0");
			uvm_report_mock::expect_error("master_checker_0", "unexpected SCE (symbol count error) flag in packet header of packet index 6 at channel 0, expected 1, read 0");
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("pdcm_denso_tdma_scheme_symbol_count_error_test")
			dsi3_pdcm_packet packets[$]; 
			tdma_scheme_pdcm_denso denso_scheme = new();
			denso_scheme.valid = 1'b1;
			tdma_scheme_upload_listener::schemes[0] = denso_scheme;
			
			repeat(7) packets.push_back(create_pdcm_packet(8, dsi3_pkg::SID_8Bit));	
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'hC401, 16'h1000},
																		{16'h0800, 16'hC401});
			fork			
				begin			
					send_pdcm_pulse(2'b01);
					#1100us;
				end
				begin
					#50us;
					foreach(packets[i]) begin
						if(i == 3) begin
							send_slave_response(2'b01, {packets[i].data, 4'ha}); // send one more symbol
						end 
						else begin
							send_slave_response(2'b01, packets[i].data);
						end
						#135us;
					end
				end
			join
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
					{16'h0804, 16'h4400, 
						16'h0007, 
							16'h0008, packets[0].get_word(0), packets[0].get_word(1),
							16'h0008, packets[1].get_word(0), packets[1].get_word(1),
							16'h0008, packets[2].get_word(0), packets[2].get_word(1),
							16'h2009, packets[3].get_word(0), packets[3].get_word(1),
							16'h0008, packets[4].get_word(0), packets[4].get_word(1),
							16'h0008, packets[5].get_word(0), packets[5].get_word(1),
							16'h0008, packets[6].get_word(0), packets[6].get_word(1)});
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("pdcm_clear_buffer_without_errors_test")
			dsi3_pdcm_packet packets[$]; 
			tdma_scheme_pdcm_denso denso_scheme = new();
			denso_scheme.valid = 1'b1;
			tdma_scheme_upload_listener::schemes[0] = denso_scheme;
			tdma_scheme_upload_listener::schemes[1] = denso_scheme;
			
			repeat(7) packets.push_back(create_pdcm_packet(8, dsi3_pkg::SID_8Bit));	
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'hCC01, 16'h1000},
																		{16'h0000, 16'hCC01});
			fork			
				begin			
					send_pdcm_pulse(2'b11);
					#1100us;
				end
				begin
					#50us;
					foreach(packets[i]) begin
						send_slave_response(2'b11, packets[i].data);
						#135us;
					end
				end
			join
			
			#100us;
			// clear PDCM buffer
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h7C02, 16'h1000},
																		{16'h000C, 16'h7C02});
			#10us;
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
					{16'h0000, 16'h4400, 
						16'h0000, 
							16'h0000, 16'h0000, 16'h0000,
							16'h0000, 16'h0000, 16'h0000,
							16'h0000, 16'h0000, 16'h0000,
							16'h0000, 16'h0000, 16'h0000,
							16'h0000, 16'h0000, 16'h0000,
							16'h0000, 16'h0000, 16'h0000,
							16'h0000, 16'h0000, 16'h0000});
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4800, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
					{16'h0000, 16'h4800, 
						16'h0000, 
							16'h0000, 16'h0000, 16'h0000,
							16'h0000, 16'h0000, 16'h0000,
							16'h0000, 16'h0000, 16'h0000,
							16'h0000, 16'h0000, 16'h0000,
							16'h0000, 16'h0000, 16'h0000,
							16'h0000, 16'h0000, 16'h0000,
							16'h0000, 16'h0000, 16'h0000});
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("pdcm_clear_buffer_before_first_frame_is_finished_test")
			dsi3_pdcm_packet packets[$]; 
			tdma_scheme_pdcm_denso denso_scheme = new();
			denso_scheme.valid = 1'b1;
			tdma_scheme_upload_listener::schemes[0] = denso_scheme;
			
			repeat(7) packets.push_back(create_pdcm_packet(8, dsi3_pkg::SID_8Bit));	
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'hC401, 16'h1000},
																		{16'h0800, 16'hC401});
			fork			
				begin			
					send_pdcm_pulse(2'b01);
					#300us;
					// clear PDCM buffer in the middle of first PDCM frame
					send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h7402, 16'h1000},
																				{16'h0800, 16'h7402});
					#800us;
				end
				begin
					#50us;
					foreach(packets[i]) begin
						send_slave_response(2'b01, packets[i].data);
						#135us;
					end
				end
			join
			
			// clear buffer must not have any effect on running period
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
					{16'h0804, 16'h4400, 
						16'h0007, 
							16'h0008, packets[0].get_word(0), packets[0].get_word(1),
							16'h0008, packets[1].get_word(0), packets[1].get_word(1),
							16'h0008, packets[2].get_word(0), packets[2].get_word(1),
							16'h0008, packets[3].get_word(0), packets[3].get_word(1),
							16'h0008, packets[4].get_word(0), packets[4].get_word(1),
							16'h0008, packets[5].get_word(0), packets[5].get_word(1),
							16'h0008, packets[6].get_word(0), packets[6].get_word(1)});
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================

		`SVTEST ("pdcm_read_during_running_pdcm_without_errors_test")
			dsi3_pdcm_packet packet1 = create_pdcm_packet(8, dsi3_pkg::SID_8Bit);
			dsi3_pdcm_packet packet2 = create_pdcm_packet(8, dsi3_pkg::SID_8Bit);
			dsi3_pdcm_packet packet3 = create_pdcm_packet(8, dsi3_pkg::SID_8Bit);
			
			set_tdma_scheme(2'b01, 300, {8}, {30}, {70});
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'hC403, 16'h1000},
																		{16'h0800, 16'hC403});
			fork			
				begin			
					repeat(3) begin
						send_pdcm_pulse(2'b01);
						#300us;
					end
				end
				begin
					#50us;
					send_slave_response(2'b01, packet1.data);
				end
				begin
					#300us;
					#50us;
					// read data of first period
					send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
							{16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
							{16'h0804, 16'h4400, 16'h0001, 16'h0008, packet1.get_word(0), packet1.get_word(1)});
					send_slave_response(2'b01, packet2.data);
				end
				begin
					#300us;
					#300us;
					#50us;
					// read data of second period
					send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
							{16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
							{16'h0804, 16'h4400, 16'h0001, 16'h0008, packet2.get_word(0), packet2.get_word(1)});
					send_slave_response(2'b01, packet3.data);
				end
			join
			
			#300us;			
			// read data of last period
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
					{16'h0804, 16'h4400, 16'h0001, 16'h0008, packet3.get_word(0), packet3.get_word(1)});
			
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("pdcm_read_during_first_period_test")
			dsi3_pdcm_packet packets[$]; 
			tdma_scheme_pdcm_denso denso_scheme = new();
			denso_scheme.valid = 1'b1;
			tdma_scheme_upload_listener::schemes[0] = denso_scheme;
			
			repeat(7) packets.push_back(create_pdcm_packet(8, dsi3_pkg::SID_8Bit));	
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'hC401, 16'h1000},
																		{16'h0800, 16'hC401});
			fork			
				begin			
					send_pdcm_pulse(2'b01);
					#500us;
					// read must not get data from current PDCM frame
					send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
							{16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
							{16'h0800, 16'h4400, 
								16'h0000, 
									16'h0000, 16'h0000, 16'h0000,
									16'h0000, 16'h0000, 16'h0000,
									16'h0000, 16'h0000, 16'h0000,
									16'h0000, 16'h0000, 16'h0000,
									16'h0000, 16'h0000, 16'h0000,
									16'h0000, 16'h0000, 16'h0000,
									16'h0000, 16'h0000, 16'h0000});
					#800us;
				end
				begin
					#50us;
					foreach(packets[i]) begin
						send_slave_response(2'b01, packets[i].data);
						#135us;
					end
				end
			join
			
			// clear buffer must not have any effect on running period
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
					{16'h0804, 16'h4400, 
						16'h0007, 
							16'h0008, packets[0].get_word(0), packets[0].get_word(1),
							16'h0008, packets[1].get_word(0), packets[1].get_word(1),
							16'h0008, packets[2].get_word(0), packets[2].get_word(1),
							16'h0008, packets[3].get_word(0), packets[3].get_word(1),
							16'h0008, packets[4].get_word(0), packets[4].get_word(1),
							16'h0008, packets[5].get_word(0), packets[5].get_word(1),
							16'h0008, packets[6].get_word(0), packets[6].get_word(1)});
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("pdcm_read_during_first_period_where_all_packets_are_missing_test")
			tdma_scheme_pdcm_denso denso_scheme = new();
			denso_scheme.valid = 1'b1;
			tdma_scheme_upload_listener::schemes[0] = denso_scheme;
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'hC401, 16'h1000},
																		{16'h0800, 16'hC401});
						
			send_pdcm_pulse(2'b01);
			#500us;
			// read must not get data from current PDCM frame
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
					{16'h0800, 16'h4400, 
						16'h0000, 
							16'h0000, 16'h0000, 16'h0000,
							16'h0000, 16'h0000, 16'h0000,
							16'h0000, 16'h0000, 16'h0000,
							16'h0000, 16'h0000, 16'h0000,
							16'h0000, 16'h0000, 16'h0000,
							16'h0000, 16'h0000, 16'h0000,
							16'h0000, 16'h0000, 16'h0000});
			#600us;
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
					{16'h0804, 16'h4400, 
						16'h0000, 
							16'h2000, 16'h0000, 16'h0000,
							16'h2000, 16'h0000, 16'h0000,
							16'h2000, 16'h0000, 16'h0000,
							16'h2000, 16'h0000, 16'h0000,
							16'h2000, 16'h0000, 16'h0000,
							16'h2000, 16'h0000, 16'h0000,
							16'h2000, 16'h0000, 16'h0000});
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("pdcm_stop_by_clear_command_queue_error_test")
			tdma_scheme_pdcm_denso denso_scheme = new();
			denso_scheme.valid = 1'b1;
			tdma_scheme_upload_listener::schemes[0] = denso_scheme;
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'hC403, 16'h1000},
																		{16'h0800, 16'hC403});
			
			fork
				begin
					send_pdcm_pulse(2'b01);
					#(denso_scheme.pdcm_period * 1us);
					send_pdcm_pulse(2'b01);
					#(denso_scheme.pdcm_period * 1us);
					send_pdcm_pulse(2'b01);
					#(denso_scheme.pdcm_period * 1us);
				end
				begin
					#500us;
					// clear DSI command queue
					send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h6C00, 16'h1000},
																				{16'h0800, 16'h6C00});
				end
			join
			
			uvm_report_mock::expect_error("master_checker_0", "got PDCM pulse without SPI request");
			uvm_report_mock::expect_error("master_checker_0", "got PDCM pulse without SPI request");
			verify_uvm_errors();
		`SVTEST_END

		//=============================================================================
		
		`SVTEST ("pdcm_stop_by_clear_command_queue_directly_after_pdcm_pulse_error_test")
			tdma_scheme_pdcm_denso denso_scheme = new();
			denso_scheme.valid = 1'b1;
			tdma_scheme_upload_listener::schemes[0] = denso_scheme;
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'hC403, 16'h1000},
																		{16'h0800, 16'hC403});
			
			fork
				begin
					send_pdcm_pulse(2'b01);
					#((denso_scheme.pdcm_period) * 1us);
					send_pdcm_pulse(2'b01);
					#((denso_scheme.pdcm_period) * 1us);
					send_pdcm_pulse(2'b01);
					#((denso_scheme.pdcm_period) * 1us);
				end
				begin
					// clear DSI command queue
					#((denso_scheme.pdcm_period) * 1us);
					#4us;
					send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h6C00, 16'h1000},
																				{16'h0804, 16'h6C00});
				end
			join
			
			uvm_report_mock::expect_error("master_checker_0", "got PDCM pulse without SPI request");
			verify_uvm_errors();
		`SVTEST_END
	
		//=============================================================================
		
		`SVTEST ("pdcm_stop_by_clear_command_queue_directly_after_pdcm_pulse_without_error_test")
			tdma_scheme_pdcm_denso denso_scheme = new();
			denso_scheme.valid = 1'b1;
			tdma_scheme_upload_listener::schemes[0] = denso_scheme;
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'hC403, 16'h1000},
																		{16'h0800, 16'hC403});
			fork
				begin
					send_pdcm_pulse(2'b01);
					#((denso_scheme.pdcm_period) * 1us);
					send_pdcm_pulse(2'b01);
					#((denso_scheme.pdcm_period) * 1us);
				end
				begin
					// clear DSI command queue
					#((denso_scheme.pdcm_period) * 1us);
					#4us;
					send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h6C00, 16'h1000},
																				{16'h0804, 16'h6C00});
				end
			join
			#200us;
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, IDLE)
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].state, IDLE)
			
			verify_uvm_errors();
		`SVTEST_END
	
	
		//=============================================================================
		
		`SVTEST ("pdcm_stop_infinite_pdcm_without_error_test")
			tdma_scheme_pdcm_denso denso_scheme = new();
			denso_scheme.valid = 1'b1;
			tdma_scheme_upload_listener::schemes[0] = denso_scheme;
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'hC400, 16'h1000},
																		{16'h0800, 16'hC400});
			
			send_pdcm_pulse(2'b01);
			#((denso_scheme.pdcm_period) * 1us);
			send_pdcm_pulse(2'b01);
			#((denso_scheme.pdcm_period) * 1us);
			send_pdcm_pulse(2'b01);
			#((denso_scheme.pdcm_period) * 1us);
			send_pdcm_pulse(2'b01);
			#((denso_scheme.pdcm_period) * 1us);
			send_pdcm_pulse(2'b01);
			#100us;
			// stop
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h6C00, 16'h1000},
																		{16'h0804, 16'h6C00});
			#((denso_scheme.pdcm_period) * 1us);
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[0].state, IDLE)
			`FAIL_UNLESS_EQUAL(m_top_config.m_master_transmission_checker[1].state, IDLE)
			
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================

		`SVTEST ("pdcm_expect_symbol_coding_error_test")
			dsi3_pdcm_packet packet1 = create_pdcm_packet(8, dsi3_pkg::SID_8Bit);
			dsi3_pdcm_packet packet2 = create_pdcm_packet(8, dsi3_pkg::SID_8Bit);
			set_tdma_scheme(2'b01, 1000, {8, 8}, {30, 152}, {70, 192});
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'hC401, 16'h1000},
																		{16'h0800, 16'hC401});

			// expect SE in at packet index 1
			checker_config::get().expect_PDCM_symbol_coding_error_in_dsi_packet[0] = {1};
			
			fork			
				begin			
					send_pdcm_pulse(2'b01);
					#1100us;
				end
				begin
					#50us;
					send_slave_response(2'b01, packet1.data);
				end
				begin
					#172us;
					send_slave_response(2'b01, packet2.data);
				end
			join
			
			// clear CRM buffer must not have any effect
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h7C01, 16'h1000},
																		{16'h0804, 16'h7C01});
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 16'h4000, 16'h4000,            16'h4000,            16'h4000, 16'h4000, 16'h4000, 16'h1000},
					{16'h0804, 16'h4400, 16'h0002, 16'h0408, packet1.get_word(0), packet1.get_word(1), 16'h0408, packet2.get_word(0), packet2.get_word(1)});
			
			checker_config::get().expect_PDCM_symbol_coding_error_in_dsi_packet[0] = {};
			
			// only packet at index 1 is expected to have a SE flag
			uvm_report_mock::expect_error("master_checker_0", "unexpected SE (symbol coding error) flag in packet header of packet index 0 at channel 0, expected 0, read 1");
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================

		`SVTEST ("pdcm_read_with_symbol_coding_errors_test")
			set_tdma_scheme(2'b01, 300, {8}, {30}, {70});
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'hC401, 16'h1000},
																		{16'h0800, 16'hC401});
			fork			
				begin			
					send_pdcm_pulse(2'b01);
					#300us;
				end
				begin
					#50us;
					send_slave_response(2'b01, {4'h3, 4'h0, 4'h7, 4'hc,  4'h2, 4'hx, 4'h4, 4'hd});
				end
			join
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
					{16'h0804, 16'h4400, 16'h0001, 16'h0008, 16'h307c, 16'h204d});
			
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================

		`SVTEST ("pdcm_slave_response_without_pdcm_pulse_test")
			set_tdma_scheme(2'b01, 300, {8}, {30}, {70});
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'hC401, 16'h1000},
																		{16'h0800, 16'hC401});
			#50us;
			send_slave_response(2'b01, {4'h3, 4'h0, 4'h7, 4'hc,  4'h2, 4'hx, 4'h4, 4'hd});
			
			// clear DSI command queue
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h6400, 16'h1000},
																		{16'h0800, 16'h6400});
			
			uvm_report_mock::expect_error("master_checker_0", "unexpected PDCM slave transaction, checker is not in PDCM state");
			verify_uvm_errors();
		`SVTEST_END
		
		
		//=============================================================================
		
		`SVTEST ("pdcm_fill_buffer_test")
			dsi3_pdcm_packet packets[$];
			int buffer_full_index = int'($floor((project_pkg::SIZE_DSI_PDCM_BUF - 16'd1) / 16'd4)); // 1 frame header + 1 packet header + 2 data words per period stored in buffer
			int buffer_warn_index = int'($floor(buffer_full_index * 0.75));
			
			repeat(260) packets.push_back(create_pdcm_packet(8, dsi3_pkg::SID_8Bit));	
			set_tdma_scheme(2'b01, 200, {8}, {30}, {70});
			
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'hC400, 16'h1000},
																		{16'h0800, 16'hC400});
			fork			
				begin
					repeat(260) begin
						send_pdcm_pulse(2'b01);
						#200us;
					end
					// clear DSI command queue
					send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'h6C00, 16'h1000},
																				{16'h4804, 16'h6C00});
				end
				begin
					#50us;
					foreach(packets[i]) begin
						send_slave_response(2'b01, packets[i].data);
						#200us;
					end
				end
			join
			
			for (int i = 0; i < 260; i++) begin
				flags_container #(spi_status_word_flags) flags = new();
				flags.set_flags({NT1});
				if(i < 255) flags.set_flags({PD0});
				if(i < 255) begin
					send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
							{               16'h4400, 16'h4000, 16'h4000, 16'h4000,               16'h4000,              16'h1000},
							{16'(flags.get_values()), 16'h4400, 16'h0001, 16'h0008, packets[i].get_word(0), packets[i].get_word(1)});
				end
				else begin
					send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
							{               16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
							{16'(flags.get_values()), 16'h4400, 16'h0000, 16'h0000, 16'h0000, 16'h0000});
				end
			end

			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================

		`SVTEST ("pdcm_receive_packet_with_more_than_255_symbols_test")
			dsi3_pdcm_packet packet1 = create_pdcm_packet(256, dsi3_pkg::SID_8Bit, 1'b1);
			logic[15:0] read_in[$] = {};
			logic[15:0] read_out[$] = {};
			
			set_tdma_scheme(2'b01, 3000, {255}, {30}, {70});
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'hC401, 16'h1000},
																		{16'h0800, 16'hC401});
			fork			
				begin			
					send_pdcm_pulse(2'b01);
					#3000us;
				end
				begin
					#50us;
					send_slave_response(2'b01, packet1.data);
				end
			join
			#50us;
			
			`FAIL_UNLESS_EQUAL(64, packet1.get_word_count())
			
			read_in.push_back(16'h4400);
			read_in.push_back(16'h4000);
			read_in.push_back(16'h4000);
			
			read_out.push_back(16'h0804);
			read_out.push_back(16'h4400);
			read_out.push_back(16'h0001); // frame header
			read_out.push_back(16'h30ff); // packet header
			
			for (int i = 0; i < 64; i++) begin
				read_out.push_back(packet1.get_word(i));
				read_in.push_back(16'h4000);
			end	
			read_in.push_back(16'h1000);
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, read_in, read_out);
			
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================

		`SVTEST ("pdcm_incomplete_read_without_errors_1_word_test")
			dsi3_pdcm_packet packet1 = create_pdcm_packet(8, dsi3_pkg::SID_8Bit);
			dsi3_pdcm_packet packet2 = create_pdcm_packet(8, dsi3_pkg::SID_8Bit);
			
			do_pdcm_channel_0_two_pulses(packet1, packet2);
			
			// read one word less than needed
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h1000},
					{16'h0804, 16'h4400});
			// read all words
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 16'h4000, 16'h4000,            16'h4000,            16'h1000},
					{16'h0804, 16'h4400, 16'h0001, 16'h0008, packet2.get_word(0), packet2.get_word(1)});
			
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================

		`SVTEST ("pdcm_incomplete_read_without_errors_2_words_test")
			dsi3_pdcm_packet packet1 = create_pdcm_packet(8, dsi3_pkg::SID_8Bit);
			dsi3_pdcm_packet packet2 = create_pdcm_packet(8, dsi3_pkg::SID_8Bit);
			
			do_pdcm_channel_0_two_pulses(packet1, packet2);
			
			// read one word less than needed
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 16'h1000},
					{16'h0804, 16'h4400, 16'h0001});
			// read all words
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
					{16'h0804, 16'h4400, 16'h0001, 16'h0008, packet2.get_word(0), packet2.get_word(1)});
			
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================

		`SVTEST ("pdcm_incomplete_read_without_errors_3_words_test")
			dsi3_pdcm_packet packet1 = create_pdcm_packet(8, dsi3_pkg::SID_8Bit);
			dsi3_pdcm_packet packet2 = create_pdcm_packet(8, dsi3_pkg::SID_8Bit);
			
			do_pdcm_channel_0_two_pulses(packet1, packet2);
			
			// read one word less than needed
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 16'h4000, 16'h1000},
					{16'h0804, 16'h4400, 16'h0001, 16'h0008});
			// read all words
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
					{16'h0804, 16'h4400, 16'h0001, 16'h0008, packet2.get_word(0), packet2.get_word(1)});
			
			verify_uvm_errors();
		`SVTEST_END
		
		//=============================================================================

		`SVTEST ("pdcm_incomplete_read_without_errors_4_test")
			dsi3_pdcm_packet packet1 = create_pdcm_packet(8, dsi3_pkg::SID_8Bit);
			dsi3_pdcm_packet packet2 = create_pdcm_packet(8, dsi3_pkg::SID_8Bit);
			
			do_pdcm_channel_0_two_pulses(packet1, packet2);
			
			// read one word less than needed
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
					{16'h0804, 16'h4400, 16'h0001, 16'h0008, packet1.get_word(0)});
			// read all words
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000},
					{16'h0804, 16'h4400, 16'h0001, 16'h0008, packet2.get_word(0), packet2.get_word(1)});
			
			verify_uvm_errors();
		`SVTEST_END
		
	`SVUNIT_TESTS_END
		
		
	task do_pdcm_channel_0_two_pulses(dsi3_pdcm_packet packet1, dsi3_pdcm_packet packet2);
		set_tdma_scheme(2'b01, 300, {8}, {30}, {70});
		send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	{16'hC402, 16'h1000},
																	{16'h0800, 16'hC402});
		fork			
			begin			
				repeat(2) begin
					send_pdcm_pulse(2'b01);
					#300us;
				end
			end
			begin
				#50us;
				send_slave_response(2'b01, packet1.data);
			end
			begin
				#350us;
				send_slave_response(2'b01, packet2.data);
			end
		join
	endtask
		
endmodule
