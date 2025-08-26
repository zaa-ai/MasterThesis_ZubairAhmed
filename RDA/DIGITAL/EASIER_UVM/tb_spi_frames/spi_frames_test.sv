`include "svunit_defines.svh"

module spi_frames_test import project_pkg::*; ();
	
	`include "uvm_macros.svh"
	
	import svunit_pkg::svunit_testcase;
	import svunit_uvm_mock_pkg::*;
	import common_env_pkg::*;
	import addresses_pkg::*;
	
	import uvm_pkg::*;
	import spi_pkg::*;
	import spi_frames_unit_test_pkg::*;

	string name = "spi_test";
	svunit_testcase svunit_ut;
	
	top_config		m_top_config;
	
	initial begin
		m_top_config = new("_top_config");
		uvm_config_db #(top_config)::set(null, "uvm_test_top", "m_top_config", m_top_config);
		uvm_config_db #(top_config)::set(null, "uvm_test_top.m_env", "m_top_config", m_top_config);
		run_test();
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
		#1us;
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
	
	/*###   test cases   ######################################################*/
	`SVUNIT_TESTS_BEGIN
	
		`SVTEST ("spi_crc_calculation_example_test")
			logic[15:0] crc = crc_calculation_pkg::spi_calculate_correct_crc({16'h8400, 16'h1d00, 16'h1e00, 16'h1000});
			`INFO($sformatf("CRC: %04h",crc));	
		`SVTEST_END
	
		`SVTEST ("spi_shortest_possible_frame_test")
			spi_tx_crc_request_seq crc_seq;
			spi_command_frame_seq frame;
			logic[15:0] data_in[$]  = {16'h1000};
			logic[15:0] data_out[$] = {16'h0000};
			logic[15:0] mosi_crc = crc_calculation_pkg::spi_calculate_correct_crc(data_in);
			logic[15:0] miso_crc = crc_calculation_pkg::spi_calculate_correct_crc(data_out);
			
			m_top_config.clear();
			send_spi_tr(m_top_config.m_spi_protocol_listener, 	{data_in,  mosi_crc}, 
																{data_out, miso_crc});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_frame_subscriber.frames.size(), 1)
			frame = m_top_config.m_spi_frame_subscriber.frames[0];	
			`FAIL_UNLESS_EQUAL(frame.commands.size(), 1)
			
			`FAIL_UNLESS_EQUAL($cast(crc_seq, frame.commands[0]), 1)
			
			`FAIL_UNLESS_EQUAL(crc_seq.get_word_count(), 2)
			`FAIL_UNLESS_EQUAL(crc_seq.mosi_crc, mosi_crc)
			`FAIL_UNLESS_EQUAL(crc_seq.mosi_crc_correct, 1)
			`FAIL_UNLESS_EQUAL(crc_seq.miso_crc, miso_crc)
			`FAIL_UNLESS_EQUAL(crc_seq.miso_crc_correct, 1)
			
			// check data_in queue
			`FAIL_UNLESS_EQUAL(frame.data_in.size(), 2)
			`FAIL_UNLESS_EQUAL(frame.data_in[0][15:12], 4'h1)
			`FAIL_UNLESS_EQUAL(frame.data_in[1], mosi_crc)
			
			// check data_out queue
			`FAIL_UNLESS_EQUAL(frame.data_out.size(), 2)
			`FAIL_UNLESS_EQUAL(frame.data_out[0], 16'h0000)
			`FAIL_UNLESS_EQUAL(frame.data_out[1], miso_crc)
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("spi_single_tx_crc_test")
			spi_command_frame_seq frame = new();
			spi_tx_crc_request_seq crc_seq = new();
			logging_spi_sequencer sequencer = m_top_config.m_sequencer;
	
			m_top_config.clear();
			`FAIL_IF_EQUAL(crc_seq.randomize() with { mosi_crc_correct == 1'b1;}, 0)
			crc_seq.mosi_crc_enable = 1'b1;
			
			sequencer.data_out = {16'h0000, crc_calculation_pkg::spi_calculate_correct_crc({16'h0000})};
			sequencer.m_config.csb_handler = per_frame_csb_hander::create();
			
			frame.set_sequencer(sequencer);
			frame.add_command(crc_seq);
			frame.body();
			
			// check data_in queue after body
			`FAIL_UNLESS_EQUAL(frame.data_in.size(), 2)
			`FAIL_UNLESS_EQUAL(frame.data_in[0][15:12], 4'h1)
			`FAIL_UNLESS_EQUAL(frame.data_in[1], crc_calculation_pkg::spi_calculate_correct_crc({frame.data_in[0]}))
			
			// check data_out queue after body
			`FAIL_UNLESS_EQUAL(frame.data_out.size(), 2)
			`FAIL_UNLESS_EQUAL(frame.data_out[0], 16'h0000)
			`FAIL_UNLESS_EQUAL(frame.data_out[1], crc_calculation_pkg::spi_calculate_correct_crc({16'h0000}))
			
			`FAIL_UNLESS_EQUAL(sequencer.transactions.size(), 4)
			`FAIL_UNLESS_EQUAL(sequencer.transactions[0].tr_type, spi_pkg::SPI_START)
			`FAIL_UNLESS_EQUAL(sequencer.transactions[1].data_in, frame.data_in[0])
			`FAIL_UNLESS_EQUAL(sequencer.transactions[2].data_in, crc_calculation_pkg::spi_calculate_correct_crc({frame.data_in[0]}))
			`FAIL_UNLESS_EQUAL(sequencer.transactions[3].tr_type, spi_pkg::SPI_END)
		`SVTEST_END
	
		//=============================================================================

		`SVTEST ("create_spi_command_frame_crc_correct")
			spi_write_master_register_seq write_seq;
			spi_tx_crc_request_seq crc_seq;
			spi_command_frame_seq frame;
				
			m_top_config.clear();
			send_spi_tr(m_top_config.m_spi_protocol_listener,
						{16'h5001, 16'hdec0, 16'h1000, 16'haffe}, 
						{16'h0000, 16'h5001, 16'hdec0, 16'ha37f});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_frame_subscriber.frames.size(), 1)
			frame = m_top_config.m_spi_frame_subscriber.frames[0];					
						
			`FAIL_UNLESS_EQUAL(frame.commands.size(), 2)
			
			`FAIL_UNLESS_EQUAL(frame.data_in.size(), 4)
			`FAIL_UNLESS_EQUAL(frame.data_in[0], 16'h5001)
			`FAIL_UNLESS_EQUAL(frame.data_in[1], 16'hdec0)
			`FAIL_UNLESS_EQUAL(frame.data_in[2][15:12], 4'h1)
			`FAIL_UNLESS_EQUAL(frame.data_in[3], 16'haffe)
			
			`FAIL_UNLESS_EQUAL(frame.data_out.size(), 4)
			`FAIL_UNLESS_EQUAL(frame.data_out[0], 16'h0000)
			`FAIL_UNLESS_EQUAL(frame.data_out[1], 16'h5001)
			`FAIL_UNLESS_EQUAL(frame.data_out[2], 16'hdec0)
			`FAIL_UNLESS_EQUAL(frame.data_out[3], 16'ha37f)
			
			`FAIL_UNLESS_EQUAL($cast(write_seq, frame.commands[0]), 1)
			
			`FAIL_UNLESS_EQUAL(write_seq.address, 1)
			`FAIL_UNLESS_EQUAL(write_seq.data, 16'hdec0)
			`FAIL_UNLESS_EQUAL(write_seq.is_first_of_frame,  1'b1)
			`FAIL_UNLESS_EQUAL(write_seq.is_last_of_frame,  1'b0)
			
			`FAIL_UNLESS_EQUAL($cast(crc_seq, frame.commands[1]), 1)
			`FAIL_UNLESS_EQUAL(crc_seq.is_first_of_frame,  1'b0)
			`FAIL_UNLESS_EQUAL(crc_seq.is_last_of_frame,  1'b1)
			
			`FAIL_UNLESS_EQUAL(crc_seq.mosi_crc_correct,  1'b0)
			`FAIL_UNLESS_EQUAL(crc_seq.miso_crc_correct,  1'b1)
		`SVTEST_END
		
		//=============================================================================
					
		`SVTEST ("spi_tx_crc_command_check_miso_crc")
			spi_crm_seq crm_seq;
			spi_tx_crc_request_seq crc_seq;
			spi_command_frame_seq frame;
			logic[15:0] data_in[$]  = {16'h8C00, 16'h1234, 16'h5678, 16'h1000};
			logic[15:0] data_out[$] = {16'h000F, 16'h8C00, 16'h1234, 16'h5678};
			logic[15:0] mosi_crc = crc_calculation_pkg::spi_calculate_correct_crc(data_in);
			logic[15:0] miso_crc = crc_calculation_pkg::spi_calculate_correct_crc(data_out);
			
			m_top_config.clear();
			send_spi_tr(m_top_config.m_spi_protocol_listener,
						{data_in, mosi_crc}, 
						{data_out, miso_crc});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_frame_subscriber.frames.size(), 1)
			frame = m_top_config.m_spi_frame_subscriber.frames[0];	
			`FAIL_UNLESS_EQUAL(frame.commands.size(), 2)
			
			`FAIL_UNLESS_EQUAL($cast(crm_seq,frame.commands[0]), 1)
			`FAIL_UNLESS_EQUAL($cast(crc_seq, frame.commands[1]), 1)
			
			`FAIL_UNLESS_EQUAL(crc_seq.get_word_count(), 2)
			`FAIL_UNLESS_EQUAL(crc_seq.mosi_crc, mosi_crc)
			`FAIL_UNLESS_EQUAL(crc_seq.mosi_crc_correct, 1)
			`FAIL_UNLESS_EQUAL(crc_seq.miso_crc, miso_crc)
			`FAIL_UNLESS_EQUAL(crc_seq.miso_crc_correct, 1)
			
			// check data_in queue
			`FAIL_UNLESS_EQUAL(frame.data_in.size(), 5)
			`FAIL_UNLESS_EQUAL(frame.data_in[0], 16'h8C00)
			`FAIL_UNLESS_EQUAL(frame.data_in[1], 16'h1234)
			`FAIL_UNLESS_EQUAL(frame.data_in[2], 16'h5678)
			`FAIL_UNLESS_EQUAL(frame.data_in[3], 16'h1000)
			`FAIL_UNLESS_EQUAL(frame.data_in[4], mosi_crc)
			
			// check data_out queue
			`FAIL_UNLESS_EQUAL(frame.data_out.size(), 5)
			`FAIL_UNLESS_EQUAL(frame.data_out[0], 16'h000F)
			`FAIL_UNLESS_EQUAL(frame.data_out[1], 16'h8C00)
			`FAIL_UNLESS_EQUAL(frame.data_out[2], 16'h1234)
			`FAIL_UNLESS_EQUAL(frame.data_out[3], 16'h5678)
			`FAIL_UNLESS_EQUAL(frame.data_out[4], miso_crc)
		`SVTEST_END
		
		//=============================================================================
					
		`SVTEST ("spi_read_master_register_test")
			spi_command_frame_seq frame = new();
			spi_read_master_register_seq read_seq = new();
			spi_tx_crc_request_seq crc_seq = new();
			logging_spi_sequencer sequencer = m_top_config.m_sequencer;
			
			m_top_config.clear();
			`FAIL_IF_EQUAL(read_seq.randomize() with {address == 5; burst_addresses.size() == 0;}, 0)
			`FAIL_IF_EQUAL(crc_seq.randomize() with { mosi_crc_correct == 1'b1;}, 0)
			crc_seq.mosi_crc_enable = 1'b1;
			
			sequencer.data_out = {16'h0000, 16'h2005, 16'hCAFE, 16'h1234};
			sequencer.m_config.csb_handler = per_frame_csb_hander::create();
			
			frame.set_sequencer(sequencer);
			frame.add_command(read_seq);
			frame.add_command(crc_seq);
			frame.body();
			
			`FAIL_UNLESS_EQUAL(sequencer.transactions.size(), 6)
			
			`FAIL_UNLESS_EQUAL(sequencer.transactions[0].tr_type, spi_pkg::SPI_START)
			
			`FAIL_UNLESS_EQUAL(sequencer.transactions[1].tr_type, spi_pkg::SPI_DATA)
			`FAIL_UNLESS_EQUAL(sequencer.transactions[1].data_in, 16'h2005)
			
			`FAIL_UNLESS_EQUAL(sequencer.transactions[2].tr_type, spi_pkg::SPI_DATA)
			`FAIL_UNLESS_EQUAL(sequencer.transactions[2].data_in, 16'h2000)
			
			`FAIL_UNLESS_EQUAL(sequencer.transactions[3].tr_type, spi_pkg::SPI_DATA)
			`FAIL_UNLESS_EQUAL(sequencer.transactions[3].data_in, crc_seq.get_word(0))
			
			`FAIL_UNLESS_EQUAL(sequencer.transactions[4].tr_type, spi_pkg::SPI_DATA)
			`FAIL_UNLESS_EQUAL(sequencer.transactions[4].data_in, crc_calculation_pkg::spi_calculate_correct_crc({16'h2005, 16'h2000, crc_seq.get_word(0)}))
			
			`FAIL_UNLESS_EQUAL(sequencer.transactions[5].tr_type, spi_pkg::SPI_END)
			// expect read data to be set
			`FAIL_UNLESS_EQUAL(read_seq.data, 16'hCAFE)
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("spi_read_burst_data_test")
			spi_command_frame_seq frame = new();
			spi_read_master_register_seq read_seq = new();
			spi_tx_crc_request_seq crc_seq = new();
			logging_spi_sequencer sequencer = m_top_config.m_sequencer;
			
			m_top_config.clear();
			`FAIL_IF_EQUAL(read_seq.randomize() with {address == 5; burst_addresses.size() == 3; burst_addresses[0] == 12'h001; burst_addresses[1] == 12'h002; burst_addresses[2] == 12'h003;}, 0)
			`FAIL_IF_EQUAL(crc_seq.randomize() with { mosi_crc_correct == 1'b1;}, 0)
			crc_seq.mosi_crc_enable = 1'b1;
			
			sequencer.data_out = {16'h0000, 16'h2005, 16'hCAFE, 16'hDEAD, 16'hBEEF, 16'hAFFE};
			sequencer.m_config.csb_handler = per_frame_csb_hander::create();
			frame.set_sequencer(sequencer);
		
			frame.add_command(read_seq);
			frame.add_command(crc_seq);
			frame.body();
			
			`FAIL_UNLESS_EQUAL(sequencer.transactions.size(), 9)
			
			`FAIL_UNLESS_EQUAL(sequencer.transactions[0].tr_type, spi_pkg::SPI_START)
			`FAIL_UNLESS_EQUAL(sequencer.transactions[1].data_in, 16'h2005)
			`FAIL_UNLESS_EQUAL(sequencer.transactions[2].data_in, 16'h2001)
			`FAIL_UNLESS_EQUAL(sequencer.transactions[3].data_in, 16'h2002)
			`FAIL_UNLESS_EQUAL(sequencer.transactions[4].data_in, 16'h2003)
			`FAIL_UNLESS_EQUAL(sequencer.transactions[5].data_in, 16'h2000)
			`FAIL_UNLESS_EQUAL(sequencer.transactions[6].data_in, crc_seq.get_word(0))
			`FAIL_UNLESS_EQUAL(sequencer.transactions[7].data_in, crc_calculation_pkg::spi_calculate_correct_crc({16'h2005, 16'h2001, 16'h2002, 16'h2003, 16'h2000, crc_seq.get_word(0)}))
			`FAIL_UNLESS_EQUAL(sequencer.transactions[8].tr_type, spi_pkg::SPI_END)
			
			// expect read data to be set
			`FAIL_UNLESS_EQUAL(read_seq.data, 16'hCAFE)
			// expect burst_data to be set
			`FAIL_UNLESS_EQUAL(read_seq.burst_data.size(), 3)
			`FAIL_UNLESS_EQUAL(read_seq.burst_data[0], 16'hDEAD)
			`FAIL_UNLESS_EQUAL(read_seq.burst_data[1], 16'hBEEF)
			`FAIL_UNLESS_EQUAL(read_seq.burst_data[2], 16'hAFFE)
		`SVTEST_END

		//=============================================================================
		
		`SVTEST ("spi_read_burst_data_protocol_listener_test")
			spi_read_master_register_seq read_seq;
			spi_tx_crc_request_seq crc_seq;
			spi_command_frame_seq frame;
			logic[15:0] data_in[$]  = {16'h2005, 16'h2001, 16'h2002, 16'h2003, 16'h2000, 16'h1000};
			logic[15:0] data_out[$] = {16'h0000, 16'h2005, 16'hCAFE, 16'hDEAD, 16'hBEEF, 16'hAFFE};
			logic[15:0] mosi_crc = crc_calculation_pkg::spi_calculate_correct_crc(data_in);
			logic[15:0] miso_crc = crc_calculation_pkg::spi_calculate_correct_crc(data_out);
			
			m_top_config.clear();
			send_spi_tr(m_top_config.m_spi_protocol_listener,
						{data_in, mosi_crc}, 
						{data_out, miso_crc});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_frame_subscriber.frames.size(), 1)
			frame = m_top_config.m_spi_frame_subscriber.frames[0];	
			`FAIL_UNLESS_EQUAL(frame.commands.size(), 2)
			
			`FAIL_UNLESS_EQUAL(frame.data_in.size(), 7)
			`FAIL_UNLESS_EQUAL(frame.data_out.size(), 7)
			
			`FAIL_UNLESS_EQUAL($cast(read_seq,frame.commands[0]), 1)
			`FAIL_UNLESS_EQUAL($cast(crc_seq, frame.commands[1]), 1)
			
			`FAIL_UNLESS_EQUAL(crc_seq.get_word_count(), 2)
			`FAIL_UNLESS_EQUAL(crc_seq.mosi_crc, mosi_crc)
			`FAIL_UNLESS_EQUAL(crc_seq.mosi_crc_correct, 1)
			`FAIL_UNLESS_EQUAL(crc_seq.miso_crc, miso_crc)
			`FAIL_UNLESS_EQUAL(crc_seq.miso_crc_correct, 1)
			
			`FAIL_UNLESS_EQUAL(read_seq.address, 5)
			`FAIL_UNLESS_EQUAL(read_seq.data, 16'hCAFE)
			`FAIL_UNLESS_EQUAL(read_seq.burst_data.size(), 3)
			`FAIL_UNLESS_EQUAL(read_seq.burst_data[0], 16'hDEAD)
			`FAIL_UNLESS_EQUAL(read_seq.burst_data[1], 16'hBEEF)
			`FAIL_UNLESS_EQUAL(read_seq.burst_data[2], 16'hAFFE)
			
			`FAIL_UNLESS_EQUAL(read_seq.burst_addresses.size(), 3)
			`FAIL_UNLESS_EQUAL(read_seq.burst_addresses[0], 12'h001)
			`FAIL_UNLESS_EQUAL(read_seq.burst_addresses[1], 12'h002)
			`FAIL_UNLESS_EQUAL(read_seq.burst_addresses[2], 12'h003)
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("spi_read_burst_starts_with_zero_address_test")
			spi_read_master_register_seq read_seq;
			spi_tx_crc_request_seq crc_seq;
			spi_command_frame_seq frame;
			
			m_top_config.clear();
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 
					{16'h2000, 16'h2170, 16'h2171, 16'h2000, 16'h1000}, 
					{16'h0c00, 16'h2000, 16'h0000, 16'h0015, 16'h0016});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_frame_subscriber.frames.size(), 1)
			frame = m_top_config.m_spi_frame_subscriber.frames[0];
			
			`FAIL_UNLESS_EQUAL(frame.commands.size(), 2)
			`FAIL_UNLESS_EQUAL(frame.data_in.size(), frame.data_out.size())
			
			`FAIL_UNLESS_EQUAL($cast(read_seq,frame.commands[0]), 1)
			`FAIL_UNLESS_EQUAL($cast(crc_seq, frame.commands[1]), 1)
			
			`FAIL_UNLESS_EQUAL(read_seq.address, 12'd0)
			`FAIL_UNLESS_EQUAL(read_seq.data, 16'h0000)
			
			`FAIL_UNLESS_EQUAL(read_seq.burst_addresses.size(), 2)
			`FAIL_UNLESS_EQUAL(read_seq.burst_addresses[0], 12'h170)
			`FAIL_UNLESS_EQUAL(read_seq.burst_addresses[1], 12'h171)

			`FAIL_UNLESS_EQUAL(read_seq.burst_data.size(), 2)
			`FAIL_UNLESS_EQUAL(read_seq.burst_data[0], 16'h0015)
			`FAIL_UNLESS_EQUAL(read_seq.burst_data[1], 16'h0016)
		`SVTEST_END
			
		//=============================================================================
		
		`SVTEST ("spi_single_tx_crc_calculation_test")
			spi_command_frame_seq frame = new();
			spi_write_master_register_seq write_seq = new();
			spi_tx_crc_request_seq crc_seq = new();
			logging_spi_sequencer sequencer = m_top_config.m_sequencer;
			
			m_top_config.clear();
			`FAIL_IF_EQUAL(write_seq.randomize() with {address == 12'h400; data == 16'h001c;}, 0)
			`FAIL_IF_EQUAL(crc_seq.randomize() with { mosi_crc_correct == 1'b1;}, 0)
			crc_seq.mosi_crc_enable = 1'b1;
			
			sequencer.data_out = {16'h0000, 16'h5400, 16'h00c, 16'h6267};
			sequencer.m_config.csb_handler = per_frame_csb_hander::create();
			
			frame.set_sequencer(sequencer);
			frame.add_command(write_seq);
			frame.add_command(crc_seq);
			frame.body();
			
			`FAIL_UNLESS_EQUAL(sequencer.transactions.size(), 6)
			`FAIL_UNLESS_EQUAL(sequencer.transactions[0].tr_type, spi_pkg::SPI_START)
			`FAIL_UNLESS_EQUAL(sequencer.transactions[1].data_in, 16'h5400)
			`FAIL_UNLESS_EQUAL(sequencer.transactions[2].data_in, 16'h001c)
			`FAIL_UNLESS_EQUAL(sequencer.transactions[3].data_in, crc_seq.get_word(0))
			`FAIL_UNLESS_EQUAL(sequencer.transactions[4].data_in, crc_calculation_pkg::spi_calculate_correct_crc({16'h5400, 16'h001c, crc_seq.get_word(0)}))
			`FAIL_UNLESS_EQUAL(sequencer.transactions[5].tr_type, spi_pkg::SPI_END)
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("spi_multipe_tx_crc_calculation_test")
			spi_command_frame_seq frame = new();
			spi_write_master_register_seq write1_seq = new();
			spi_write_master_register_seq write2_seq = new();
			spi_tx_crc_request_seq crc1_seq = new();
			spi_tx_crc_request_seq crc2_seq = new();
			logging_spi_sequencer sequencer = m_top_config.m_sequencer;

			m_top_config.clear();
			`FAIL_IF_EQUAL(write1_seq.randomize() with {address == 12'h400; data == 16'h001c;}, 0)
			`FAIL_IF_EQUAL(crc1_seq.randomize() with { mosi_crc_correct == 1'b1;}, 0)
			crc1_seq.mosi_crc_enable = 1'b1;
			`FAIL_IF_EQUAL(write2_seq.randomize() with {address == 12'h400; data == 16'h001c;}, 0)
			`FAIL_IF_EQUAL(crc2_seq.randomize() with { mosi_crc_correct == 1'b1;}, 0)
			crc2_seq.mosi_crc_enable = 1'b1;
			
			sequencer.data_out = {16'h0000, 16'h5400, 16'h00c, 16'h6267, 16'h0000, 16'h5400, 16'h00c, 16'h6267};
			sequencer.m_config.csb_handler = per_frame_csb_hander::create();
			
			frame.set_sequencer(sequencer);
			frame.add_command(write1_seq);
			frame.add_command(crc1_seq);
			frame.add_command(write2_seq);
			frame.add_command(crc2_seq);

			frame.body();
			
			`FAIL_UNLESS_EQUAL(sequencer.transactions.size(), 10)
			`FAIL_UNLESS_EQUAL(sequencer.transactions[0].tr_type, spi_pkg::SPI_START)
			`FAIL_UNLESS_EQUAL(sequencer.transactions[1].data_in, 16'h5400)
			`FAIL_UNLESS_EQUAL(sequencer.transactions[2].data_in, 16'h001c)
			`FAIL_UNLESS_EQUAL(sequencer.transactions[3].data_in, crc1_seq.get_word(0))
			`FAIL_UNLESS_EQUAL(sequencer.transactions[4].data_in, crc_calculation_pkg::spi_calculate_correct_crc({16'h5400, 16'h001c, crc1_seq.get_word(0)}))
			`FAIL_UNLESS_EQUAL(sequencer.transactions[5].data_in, 16'h5400)
			`FAIL_UNLESS_EQUAL(sequencer.transactions[6].data_in, 16'h001c)
			`FAIL_UNLESS_EQUAL(sequencer.transactions[7].data_in, crc2_seq.get_word(0))
			`FAIL_UNLESS_EQUAL(sequencer.transactions[8].data_in, crc_calculation_pkg::spi_calculate_correct_crc({16'h5400, 16'h001c, crc2_seq.get_word(0)}))
			`FAIL_UNLESS_EQUAL(sequencer.transactions[9].tr_type, spi_pkg::SPI_END)
		`SVTEST_END
		
		//=============================================================================

		`SVTEST ("spi_transaction_word_index_test")
			spi_command_frame_seq frame = new();
			spi_read_master_register_seq read1_seq = new();
			spi_read_master_register_seq read2_seq = new();
			logging_spi_sequencer sequencer = m_top_config.m_sequencer;

			m_top_config.clear();
			`FAIL_IF_EQUAL(read1_seq.randomize() with {burst_addresses.size() == 0;}, 0)
			`FAIL_IF_EQUAL(read2_seq.randomize() with {burst_addresses.size() == 0;}, 0)
			
			sequencer.m_config.csb_handler = per_frame_csb_hander::create();
			
			frame.set_sequencer(sequencer);
			frame.add_command(read1_seq);
			frame.add_command(read2_seq);
			frame.body();
			
			`FAIL_UNLESS_EQUAL(sequencer.transactions.size(), 6)
			`FAIL_UNLESS_EQUAL(sequencer.transactions[0].word_index, -1)
			`FAIL_UNLESS_EQUAL(sequencer.transactions[1].word_index,  0)
			`FAIL_UNLESS_EQUAL(sequencer.transactions[2].word_index,  1)
			`FAIL_UNLESS_EQUAL(sequencer.transactions[3].word_index,  2)
			`FAIL_UNLESS_EQUAL(sequencer.transactions[4].word_index,  3)
			`FAIL_UNLESS_EQUAL(sequencer.transactions[5].word_index, -1)
		`SVTEST_END
		
		//=============================================================================
					
		`SVTEST ("upload_tdma_scheme_test")
			spi_upload_tdma_packet_seq upload_seq;
			spi_validate_tdma_scheme_seq validate_seq;
			spi_tx_crc_request_seq crc_seq;
			spi_command_frame_seq frame;
			
			m_top_config.clear();
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener,
						{16'hbc20, 16'h001e, 16'h0046, 16'h8008, 16'hbcc1, 16'h012c, 16'h15dd}, 
						{16'h0000, 16'hbc20, 16'h001e, 16'h0046, 16'h8008, 16'hbcc1, 16'h012c});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_frame_subscriber.frames.size(), 1)
			frame = m_top_config.m_spi_frame_subscriber.frames[0];	
			`FAIL_UNLESS_EQUAL(frame.commands.size(), 3)
			
			`FAIL_UNLESS_EQUAL($cast(upload_seq, 	frame.commands[0]), 1)
			`FAIL_UNLESS_EQUAL($cast(validate_seq, 	frame.commands[1]), 1)
			`FAIL_UNLESS_EQUAL($cast(crc_seq, 		frame.commands[2]), 1)
			
			`FAIL_UNLESS_EQUAL(upload_seq.channel_bits, 2'b11)
			`FAIL_UNLESS_EQUAL(upload_seq.packet_index, 0)
			`FAIL_UNLESS_EQUAL(upload_seq.tdma_packet.earliest_start_time, 30)
			`FAIL_UNLESS_EQUAL(upload_seq.tdma_packet.latest_start_time, 70)
			`FAIL_UNLESS_EQUAL(upload_seq.tdma_packet.symbol_count, 8)
			`FAIL_UNLESS_EQUAL(upload_seq.tdma_packet.id_symbol_count, 2)
			
			`FAIL_UNLESS_EQUAL(validate_seq.channel_bits, 2'b11)
			`FAIL_UNLESS_EQUAL(validate_seq.packet_count, 1)
			`FAIL_UNLESS_EQUAL(validate_seq.pdcm_period, 300)
		`SVTEST_END	
		
		//=============================================================================
		
		`SVTEST ("spi_read_crm_data_packets_single_channel_test")
			spi_read_crm_data_packets_seq read_seq = new();
			spi_tx_crc_request_seq crc_seq;
			spi_command_frame_seq frame;
			m_top_config.clear();
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener,
					{16'h385e, 16'h3705, 16'h3b01, 16'h3c20, 16'h167f},
					{16'h0000, 16'h385e, 16'h1008, 16'h1234, 16'h5678});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_frame_subscriber.frames.size(), 1)
			frame = m_top_config.m_spi_frame_subscriber.frames[0];	
			`FAIL_UNLESS_EQUAL(frame.commands.size(), 2)
			
			`FAIL_UNLESS_EQUAL($cast(read_seq,	frame.commands[0]), 1)
			`FAIL_UNLESS_EQUAL($cast(crc_seq, 	frame.commands[1]), 1)
			
			`FAIL_UNLESS_EQUAL(read_seq.data_packets.size(), 1)
			check_data_packet(read_seq.data_packets[0], 2'd1, 8'd8, {16'h1234, 16'h5678});
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].get_value(SCE), 1'b0)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].get_value(CRC), 1'b1)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].get_value(TE),  1'b0)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].get_value(SE),  1'b0)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].get_value(VE),  1'b0)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].get_value(CE),  1'b0)
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("spi_read_crm_data_packets_both_channels_test")
			spi_read_crm_data_packets_seq read_seq = new();
			spi_tx_crc_request_seq crc_seq;
			spi_command_frame_seq frame;
			m_top_config.clear();
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener,
					{16'h3c5e, 16'h3705, 16'h3b01, 16'h3c20, 16'h3705, 16'h3b01, 16'h3c20, 16'h167f},
					{16'h0000, 16'h3c5e, 16'h1008, 16'h1234, 16'h5678, 16'h0008, 16'h9abc, 16'hdef0});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_frame_subscriber.frames.size(), 1)
			frame = m_top_config.m_spi_frame_subscriber.frames[0];	
			`FAIL_UNLESS_EQUAL(frame.commands.size(), 2)
			
			`FAIL_UNLESS_EQUAL($cast(read_seq,	frame.commands[0]), 1)
			`FAIL_UNLESS_EQUAL($cast(crc_seq, 	frame.commands[1]), 1)
			
			`FAIL_UNLESS_EQUAL(read_seq.data_packets.size(), 2)
			check_data_packet(read_seq.data_packets[0], 2'd0, 8'd8, {16'h1234, 16'h5678});
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].get_value(SCE), 1'b0)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].get_value(CRC), 1'b1)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].get_value(TE),  1'b0)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].get_value(SE),  1'b0)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].get_value(VE),  1'b0)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].get_value(CE),  1'b0)
			
			check_data_packet(read_seq.data_packets[1], 2'd1, 8'd8, {16'h9abc, 16'hdef0});
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[1].get_value(SCE), 1'b0)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[1].get_value(CRC), 1'b0)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[1].get_value(TE),  1'b0)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[1].get_value(SE),  1'b0)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[1].get_value(VE),  1'b0)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[1].get_value(CE),  1'b0)
		`SVTEST_END	
		
		//=============================================================================
		
		`SVTEST ("spi_read_pdcm_frame_single_channel_test")
			spi_read_pdcm_frame_seq read_seq = new();
			spi_tx_crc_request_seq crc_seq;
			spi_command_frame_seq frame;
			m_top_config.clear();
			
			tdma_scheme_upload_listener::schemes[0].valid = 1'b1;
			tdma_scheme_upload_listener::schemes[0].packets[0].enable = 1'b1;
			tdma_scheme_upload_listener::schemes[0].packets[0].symbol_count = 8;
			tdma_scheme_upload_listener::schemes[0].packets[1].enable = 1'b1;
			tdma_scheme_upload_listener::schemes[0].packets[1].symbol_count = 8;
			
			tdma_scheme_upload_listener::schemes[1].valid = 1'b1;
			tdma_scheme_upload_listener::schemes[1].packets[0].enable = 1'b1;
			tdma_scheme_upload_listener::schemes[1].packets[0].symbol_count = 8;
			tdma_scheme_upload_listener::schemes[1].packets[1].enable = 1'b1;
			tdma_scheme_upload_listener::schemes[1].packets[1].symbol_count = 8;
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener,
					{16'h481d, 16'h4bf4, 16'h4099, 16'h47e3, 16'h4207, 16'h4d80, 16'h45e8, 16'h4308, 16'h1b35},
					{16'h0000, 16'h481d, 16'h0002, 16'h0008, 16'h1234, 16'h5678, 16'h0008, 16'hdead, 16'haffe});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_frame_subscriber.frames.size(), 1)
			frame = m_top_config.m_spi_frame_subscriber.frames[0];	
			`FAIL_UNLESS_EQUAL(frame.commands.size(), 2)
			
			`FAIL_UNLESS_EQUAL($cast(read_seq,	frame.commands[0]), 1)
			`FAIL_UNLESS_EQUAL($cast(crc_seq, 	frame.commands[1]), 1)
			
			`FAIL_UNLESS_EQUAL(read_seq.frame_header.size(), 1)
			`FAIL_UNLESS_EQUAL(read_seq.frame_header[0].packet_count, 2)
			`FAIL_UNLESS_EQUAL(read_seq.frame_header[0].channel_index, 2'b1)
			
			`FAIL_UNLESS_EQUAL(read_seq.data_packets.size(), 2)
			check_data_packet(read_seq.data_packets[0], 2'd1, 8'd8, {16'h1234, 16'h5678});
			check_data_packet(read_seq.data_packets[1], 2'd1, 8'd8, {16'hdead, 16'haffe});
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("spi_read_pdcm_frame_both_channels_test")
			spi_read_pdcm_frame_seq read_seq = new();
			spi_tx_crc_request_seq crc_seq;
			spi_command_frame_seq frame;
			m_top_config.clear();
			
			tdma_scheme_upload_listener::schemes[0].valid = 1'b1;
			tdma_scheme_upload_listener::schemes[0].packets[0].enable = 1'b1;
			tdma_scheme_upload_listener::schemes[0].packets[0].symbol_count = 4;
			
			tdma_scheme_upload_listener::schemes[1].valid = 1'b1;
			tdma_scheme_upload_listener::schemes[1].packets[0].enable = 1'b1;
			tdma_scheme_upload_listener::schemes[1].packets[0].symbol_count = 8;
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener,
					{16'h4c1d, 16'h4bf4, 16'h4099, 16'h47e3, 16'h4207, 16'h4d80, 16'h45e8, 16'h4308, 16'h1b35},
					{16'h0000, 16'h4c1d, 16'h0001, 16'h0004, 16'h1234, 16'h0001, 16'h0008, 16'hdead, 16'haffe});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_frame_subscriber.frames.size(), 1)
			frame = m_top_config.m_spi_frame_subscriber.frames[0];	
			`FAIL_UNLESS_EQUAL(frame.commands.size(), 2)
			
			`FAIL_UNLESS_EQUAL($cast(read_seq,	frame.commands[0]), 1)
			`FAIL_UNLESS_EQUAL($cast(crc_seq, 	frame.commands[1]), 1)
			
			`FAIL_UNLESS_EQUAL(read_seq.frame_header.size(), 2)
			`FAIL_UNLESS_EQUAL(read_seq.frame_header[0].packet_count, 1)
			`FAIL_UNLESS_EQUAL(read_seq.frame_header[0].channel_index, 2'b0)
			`FAIL_UNLESS_EQUAL(read_seq.frame_header[1].packet_count, 1)
			`FAIL_UNLESS_EQUAL(read_seq.frame_header[1].channel_index, 2'b1)
			
			`FAIL_UNLESS_EQUAL(read_seq.data_packets.size(), 2)
			check_data_packet(read_seq.data_packets[0], 2'd0, 8'd4, {16'h1234});
			check_data_packet(read_seq.data_packets[1], 2'd1, 8'd8, {16'hdead, 16'haffe});			
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("spi_read_pdcm_frame_single_channel_word_alignment_test")
			spi_read_pdcm_frame_seq read_seq = new();
			spi_tx_crc_request_seq crc_seq;
			spi_command_frame_seq frame;
			m_top_config.clear();
			
			tdma_scheme_upload_listener::schemes[0].valid = 1'b1;
			tdma_scheme_upload_listener::schemes[0].packets[0].enable = 1'b1;
			tdma_scheme_upload_listener::schemes[0].packets[0].symbol_count = 5;
			tdma_scheme_upload_listener::schemes[0].packets[1].enable = 1'b1;
			tdma_scheme_upload_listener::schemes[0].packets[1].symbol_count = 7;
			
			tdma_scheme_upload_listener::schemes[1].valid = 1'b1;
			tdma_scheme_upload_listener::schemes[1].packets[0].enable = 1'b1;
			tdma_scheme_upload_listener::schemes[1].packets[0].symbol_count = 8;
			tdma_scheme_upload_listener::schemes[1].packets[1].enable = 1'b1;
			tdma_scheme_upload_listener::schemes[1].packets[1].symbol_count = 8;
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 
					{16'h481d, 16'h4bf4, 16'h4099, 16'h47e3, 16'h4207, 16'h4d80, 16'h45e8, 16'h4308, 16'h1b35},
					{16'h0000, 16'h481d, 16'h0002, 16'h0005, 16'h1234, 16'h5000, 16'h0007, 16'hdead, 16'haff0});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_frame_subscriber.frames.size(), 1)
			frame = m_top_config.m_spi_frame_subscriber.frames[0];	
			`FAIL_UNLESS_EQUAL(frame.commands.size(), 2)
			
			`FAIL_UNLESS_EQUAL($cast(read_seq,	frame.commands[0]), 1)
			`FAIL_UNLESS_EQUAL($cast(crc_seq, 	frame.commands[1]), 1)
			
			`FAIL_UNLESS_EQUAL(read_seq.frame_header.size(), 1)
			`FAIL_UNLESS_EQUAL(read_seq.frame_header[0].packet_count, 2)
			`FAIL_UNLESS_EQUAL(read_seq.frame_header[0].channel_index, 2'b1)
			
			`FAIL_UNLESS_EQUAL(read_seq.data_packets.size(), 2)
			check_data_packet(read_seq.data_packets[0], 2'd1, 8'd5, {16'h1234, 16'h5000});
			check_data_packet(read_seq.data_packets[1], 2'd1, 8'd7, {16'hdead, 16'haff0});
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("spi_read_pdcm_frame_without_valid_scheme_both_channels_test")
			spi_read_pdcm_frame_seq read_seq = new();
			spi_tx_crc_request_seq crc_seq;
			spi_command_frame_seq frame;
			m_top_config.clear();
			
			tdma_scheme_upload_listener::schemes[0].valid = 1'b0;
			tdma_scheme_upload_listener::schemes[1].valid = 1'b0;
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener,
					{16'h4c1d, 16'h4bf4, 16'h4099, 16'h1b35},
					{16'h0000, 16'h4c1d, 16'h0000, 16'h0000});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_frame_subscriber.frames.size(), 1)
			frame = m_top_config.m_spi_frame_subscriber.frames[0];	
			`FAIL_UNLESS_EQUAL(frame.commands.size(), 2)
			
			`FAIL_UNLESS_EQUAL($cast(read_seq,	frame.commands[0]), 1)
			`FAIL_UNLESS_EQUAL($cast(crc_seq, 	frame.commands[1]), 1)
			
			`FAIL_UNLESS_EQUAL(read_seq.frame_header.size(), 2)
			`FAIL_UNLESS_EQUAL(read_seq.frame_header[0].packet_count, 0)
			`FAIL_UNLESS_EQUAL(read_seq.frame_header[0].channel_index, 2'b0)
			`FAIL_UNLESS_EQUAL(read_seq.frame_header[1].packet_count, 0)
			`FAIL_UNLESS_EQUAL(read_seq.frame_header[1].channel_index, 2'b1)
			
			`FAIL_UNLESS_EQUAL(read_seq.data_packets.size(), 0)
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("spi_read_pdcm_frame_without_valid_scheme_single_channel_test")
			spi_read_pdcm_frame_seq read_seq = new();
			spi_tx_crc_request_seq crc_seq;
			spi_command_frame_seq frame;
			
			m_top_config.clear();
			
			tdma_scheme_upload_listener::schemes[0].valid = 1'b0;
			tdma_scheme_upload_listener::schemes[1].valid = 1'b0;
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h441d, 16'h4bf4, 16'h1b35},
					{16'h0000, 16'h441d, 16'h0000});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_frame_subscriber.frames.size(), 1)
			frame = m_top_config.m_spi_frame_subscriber.frames[0];	
			`FAIL_UNLESS_EQUAL(frame.commands.size(), 2)
			
			`FAIL_UNLESS_EQUAL($cast(read_seq,	frame.commands[0]), 1)
			`FAIL_UNLESS_EQUAL($cast(crc_seq, 	frame.commands[1]), 1)
			
			`FAIL_UNLESS_EQUAL(read_seq.frame_header.size(), 1)
			`FAIL_UNLESS_EQUAL(read_seq.frame_header[0].packet_count, 0)
			`FAIL_UNLESS_EQUAL(read_seq.frame_header[0].channel_index, 2'b0)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets.size(), 0)
		`SVTEST_END
		
		//=============================================================================		
		
		`SVTEST ("spi_read_crm_port_single_read_test")
			spi_read_crm_data_packets_seq read_seq;
			m_top_config.clear();
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h385e, 16'h3705, 16'h3b01, 16'h3c20, 16'h167f},
					{16'h0000, 16'h385e, 16'h1008, 16'h1234, 16'h5678});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_read_crm_subscriber.reads.size(), 1)
			read_seq = m_top_config.m_spi_read_crm_subscriber.reads[0];	
			
			`FAIL_UNLESS_EQUAL(read_seq.data_packets.size(), 1)
			check_data_packet(read_seq.data_packets[0], 2'd1, 8'd8, {16'h1234, 16'h5678});
			
			`FAIL_UNLESS_EQUAL(read_seq.get_word_count(), 4)
			`FAIL_UNLESS_EQUAL(read_seq.incomplete, 1'b0)
			`FAIL_UNLESS_EQUAL(read_seq.get_word(0), 16'h385e)
			`FAIL_UNLESS_EQUAL(read_seq.get_word(1), 16'h3705)
			`FAIL_UNLESS_EQUAL(read_seq.get_word(2), 16'h3b01)
			`FAIL_UNLESS_EQUAL(read_seq.get_word(3), 16'h3c20)
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("spi_transmit_crm_and_read_crm_port_test")
			spi_read_crm_data_packets_seq read_seq;
			m_top_config.clear();
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h8800, 16'haffe, 16'hcafe, 16'h3800, 16'h3001, 16'h3002, 16'h3003, 16'h1000},
					{16'h0000, 16'h8800, 16'haffe, 16'hcafe, 16'h3800, 16'h0008, 16'h1001, 16'h2002});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_read_crm_subscriber.reads.size(), 1)
			read_seq = m_top_config.m_spi_read_crm_subscriber.reads[0];
			
			`FAIL_UNLESS_EQUAL(read_seq.data_packets.size(), 1)
			check_data_packet(read_seq.data_packets[0], 2'd1, 8'd8, {16'h1001, 16'h2002});
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("spi_read_crm_port_multiple_reads_test")
			spi_read_crm_data_packets_seq read1_seq, read2_seq;
			m_top_config.clear();
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h3800, 16'h3001, 16'h3002, 16'h3003, 16'h3400, 16'h3004, 16'h3005, 16'h3006, 16'h1000},
					{16'h0000, 16'h385e, 16'h1008, 16'h1234, 16'h5678, 16'h3400, 16'h0008, 16'h9abc, 16'hdef0});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_read_crm_subscriber.reads.size(), 2)
			read1_seq = m_top_config.m_spi_read_crm_subscriber.reads[0];
			read2_seq = m_top_config.m_spi_read_crm_subscriber.reads[1];
			
			`FAIL_UNLESS_EQUAL(read1_seq.data_packets.size(), 1)
			check_data_packet(read1_seq.data_packets[0], 2'd1, 8'd8, {16'h1234, 16'h5678});
			
			`FAIL_UNLESS_EQUAL(read2_seq.data_packets.size(), 1)
			check_data_packet(read2_seq.data_packets[0], 2'd0, 8'd8, {16'h9abc, 16'hdef0});
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("spi_read_pdcm_port_single_read_test")
			spi_read_pdcm_frame_seq read_seq;
			m_top_config.clear();
			
			tdma_scheme_upload_listener::schemes[0].valid = 1'b1;
			tdma_scheme_upload_listener::schemes[0].packets[0].enable = 1'b1;
			tdma_scheme_upload_listener::schemes[0].packets[0].symbol_count = 4;
			tdma_scheme_upload_listener::schemes[0].packets[1].enable = 1'b0;
			
			tdma_scheme_upload_listener::schemes[1].valid = 1'b0;
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4bf4, 16'h4099, 16'h47e3, 16'h1000},
					{16'h0000, 16'h4400, 16'h0001, 16'h0004, 16'h1234});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_read_pdcm_subscriber.reads.size(), 1)
			read_seq = m_top_config.m_spi_read_pdcm_subscriber.reads[0];	
			
			`FAIL_UNLESS_EQUAL(read_seq.frame_header.size(), 1)
			`FAIL_UNLESS_EQUAL(read_seq.frame_header[0].packet_count, 1)
			`FAIL_UNLESS_EQUAL(read_seq.frame_header[0].channel_index, 2'b0)
			
			`FAIL_UNLESS_EQUAL(read_seq.data_packets.size(), 1)
			check_data_packet(read_seq.data_packets[0], 2'd0, 8'd4, {16'h1234});
			
			`FAIL_UNLESS_EQUAL(read_seq.get_word_count(), 4)
			`FAIL_UNLESS_EQUAL(read_seq.incomplete, 1'b0)
			`FAIL_UNLESS_EQUAL(read_seq.get_word(0), 16'h4400)
			`FAIL_UNLESS_EQUAL(read_seq.get_word(1), 16'h4bf4)
			`FAIL_UNLESS_EQUAL(read_seq.get_word(2), 16'h4099)
			`FAIL_UNLESS_EQUAL(read_seq.get_word(3), 16'h47e3)
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("spi_read_pdcm_port_multiple_reads_test")
			spi_read_pdcm_frame_seq read1_seq, read2_seq;
			m_top_config.clear();
			
			set_tdma_scheme(2'b11, 300, {4}, {30}, {70});
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h4400, 16'h4001, 16'h4002, 16'h4003, 16'h4800, 16'h4004, 16'h4005, 16'h4006, 16'h1000},
					{16'h0000, 16'h4400, 16'h0001, 16'h0004, 16'h1234, 16'h4800, 16'h0001, 16'h0004, 16'h5678});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_read_pdcm_subscriber.reads.size(), 2)
			read1_seq = m_top_config.m_spi_read_pdcm_subscriber.reads[0];
			read2_seq = m_top_config.m_spi_read_pdcm_subscriber.reads[1];
			
			`FAIL_UNLESS_EQUAL(read1_seq.frame_header.size(), 1)
			`FAIL_UNLESS_EQUAL(read1_seq.frame_header[0].packet_count, 1)
			`FAIL_UNLESS_EQUAL(read1_seq.frame_header[0].channel_index, 2'b0)
			`FAIL_UNLESS_EQUAL(read1_seq.data_packets.size(), 1)
			check_data_packet(read1_seq.data_packets[0], 2'd0, 8'd4, {16'h1234});
			
			`FAIL_UNLESS_EQUAL(read2_seq.frame_header.size(), 1)
			`FAIL_UNLESS_EQUAL(read2_seq.frame_header[0].packet_count, 1)
			`FAIL_UNLESS_EQUAL(read2_seq.frame_header[0].channel_index, 2'b1)
			`FAIL_UNLESS_EQUAL(read2_seq.data_packets.size(), 1)
			check_data_packet(read2_seq.data_packets[0], 2'd1, 8'd4, {16'h5678});
		`SVTEST_END

		//=============================================================================
		
		`SVTEST ("measure_quiescent_current_test")
			spi_measure_quiescent_current_seq measure_seq;
			spi_tx_crc_request_seq crc_seq;
			spi_command_frame_seq frame;
			
			m_top_config.clear();
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener,
						{16'h9c00, 16'h1000}, 
						{16'h0000, 16'h9c00});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_frame_subscriber.frames.size(), 1)
			frame = m_top_config.m_spi_frame_subscriber.frames[0];	
			`FAIL_UNLESS_EQUAL(frame.commands.size(), 2)
			
			`FAIL_UNLESS_EQUAL($cast(measure_seq, 	frame.commands[0]), 1)
			`FAIL_UNLESS_EQUAL($cast(crc_seq, 		frame.commands[2]), 1)
			`FAIL_UNLESS_EQUAL(measure_seq.channel_bits, 2'b11)
		`SVTEST_END

		//=============================================================================
		
		`SVTEST ("tx_crc_only_spi_frame_command")
			spi_tx_crc_request_seq crc_seq;
			spi_command_frame_seq frame;
			
			m_top_config.clear();
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener,
					{ 16'h1000}, 
					{ 16'h0C00});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_frame_subscriber.frames.size(), 1)
			frame = m_top_config.m_spi_frame_subscriber.frames[0];	
			`FAIL_UNLESS_EQUAL(frame.commands.size(), 1)
			`FAIL_UNLESS_EQUAL($cast(crc_seq, frame.commands[0]), 1)
			
			// check data_in queue
			`FAIL_UNLESS_EQUAL(frame.data_in.size(), 2)
			`FAIL_UNLESS_EQUAL(frame.data_in[0], 16'h1000)
			
			// check data_out queue
			`FAIL_UNLESS_EQUAL(frame.data_out.size(), 2)
			`FAIL_UNLESS_EQUAL(frame.data_out[0], 16'h0C00)
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("reset_only_spi_frame_command")
			spi_reset_seq reset_seq;
			spi_command_frame_seq frame;
			
			m_top_config.clear();
			send_spi_tr(m_top_config.m_spi_protocol_listener,
					{ 16'hFFFF, 16'hFFFF, 16'hFFFF, 16'hFFFF}, 
					{ 16'h0000, 16'hFFFF, 16'hFFFF, 16'hFFFF});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_frame_subscriber.frames.size(), 1)
			frame = m_top_config.m_spi_frame_subscriber.frames[0];	
			`FAIL_UNLESS_EQUAL(frame.commands.size(), 1)
			`FAIL_UNLESS_EQUAL($cast(reset_seq, frame.commands[0]), 1)
			
			// check data_in queue
			`FAIL_UNLESS_EQUAL(frame.data_in.size(), 4)
			`FAIL_UNLESS_EQUAL(frame.data_in[0], 16'hFFFF)
			`FAIL_UNLESS_EQUAL(frame.data_in[1], 16'hFFFF)
			`FAIL_UNLESS_EQUAL(frame.data_in[2], 16'hFFFF)
			`FAIL_UNLESS_EQUAL(frame.data_in[3], 16'hFFFF)
			
			// check data_out queue
			`FAIL_UNLESS_EQUAL(frame.data_out.size(), 4)
			`FAIL_UNLESS_EQUAL(frame.data_out[0], 16'h0000)
			`FAIL_UNLESS_EQUAL(frame.data_out[1], 16'hFFFF)
			`FAIL_UNLESS_EQUAL(frame.data_out[2], 16'hFFFF)
			`FAIL_UNLESS_EQUAL(frame.data_out[3], 16'hFFFF)
		`SVTEST_END
		
		//=============================================================================
					
		`SVTEST ("spi_frame_with_reset_command")
			spi_crm_seq crm_seq;
			spi_reset_seq reset_seq;
			spi_command_frame_seq frame;
			
			m_top_config.clear();
			send_spi_tr(m_top_config.m_spi_protocol_listener,
					{16'h8C00, 16'h1234, 16'h5678, 16'hFFFF, 16'hFFFF, 16'hFFFF, 16'hFFFF}, 
					{16'h000F, 16'h8C00, 16'h1234, 16'h5678, 16'hFFFF, 16'hFFFF, 16'hFFFF});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_frame_subscriber.frames.size(), 1)
			frame = m_top_config.m_spi_frame_subscriber.frames[0];	
			`FAIL_UNLESS_EQUAL(frame.commands.size(), 2)
			
			`FAIL_UNLESS_EQUAL($cast(crm_seq,frame.commands[0]), 1)
			`FAIL_UNLESS_EQUAL($cast(reset_seq, frame.commands[1]), 1)
			
			`FAIL_UNLESS_EQUAL(crm_seq.broad_cast, 0)
			`FAIL_UNLESS_EQUAL(crm_seq.crm_packet.get_word(0), 16'h1234)
			`FAIL_UNLESS_EQUAL(crm_seq.crm_packet.get_word(1), 16'h5678)
			
			// check data_in queue
			`FAIL_UNLESS_EQUAL(frame.data_in.size(), 7)
			`FAIL_UNLESS_EQUAL(frame.data_in[0], 16'h8C00)
			`FAIL_UNLESS_EQUAL(frame.data_in[1], 16'h1234)
			`FAIL_UNLESS_EQUAL(frame.data_in[2], 16'h5678)
			`FAIL_UNLESS_EQUAL(frame.data_in[3], 16'hFFFF)
			`FAIL_UNLESS_EQUAL(frame.data_in[4], 16'hFFFF)
			`FAIL_UNLESS_EQUAL(frame.data_in[5], 16'hFFFF)
			`FAIL_UNLESS_EQUAL(frame.data_in[6], 16'hFFFF)
			
			// check data_out queue
			`FAIL_UNLESS_EQUAL(frame.data_out.size(), 7)
			`FAIL_UNLESS_EQUAL(frame.data_out[0], 16'h000F)
			`FAIL_UNLESS_EQUAL(frame.data_out[1], 16'h8C00)
			`FAIL_UNLESS_EQUAL(frame.data_out[2], 16'h1234)
			`FAIL_UNLESS_EQUAL(frame.data_out[3], 16'h5678)
			`FAIL_UNLESS_EQUAL(frame.data_out[4], 16'hFFFF)
			`FAIL_UNLESS_EQUAL(frame.data_out[5], 16'hFFFF)
			`FAIL_UNLESS_EQUAL(frame.data_out[6], 16'hFFFF)
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("spi_frame_with_reset_command_followed_by_valid_frame")
			spi_pdcm_seq pdcm_seq;
			spi_reset_seq reset_seq;
			spi_tx_crc_request_seq crc_seq;
			spi_command_frame_seq frame;
			
			logic[15:0] valid_frame_in[$]  = {16'hCC03, 16'h1000};
			logic[15:0] valid_frame_out[$] = {16'h0000, 16'hCC03};
			
			m_top_config.clear();
			send_spi_tr(m_top_config.m_spi_protocol_listener,
					{16'hCC01, 16'hFFFF, 16'hFFFF, 16'hFFFF, 16'hFFFE,  valid_frame_in[0],  valid_frame_in[1], crc_calculation_pkg::spi_calculate_correct_crc(valid_frame_in)}, 
					{16'h000F, 16'hCC01, 16'hFFFF, 16'hFFFF, 16'hFFFF, valid_frame_out[0], valid_frame_out[1], crc_calculation_pkg::spi_calculate_correct_crc(valid_frame_out)});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_frame_subscriber.frames.size(), 2)
			
			// first frame
			frame = m_top_config.m_spi_frame_subscriber.frames[0];	
			`FAIL_UNLESS_EQUAL(frame.commands.size(), 2)
			
			`FAIL_UNLESS_EQUAL($cast(pdcm_seq,frame.commands[0]), 1)
			`FAIL_UNLESS_EQUAL(pdcm_seq.channel_bits, 2'b11)
			`FAIL_UNLESS_EQUAL(pdcm_seq.pulse_count, 1)
			
			`FAIL_UNLESS_EQUAL($cast(reset_seq, frame.commands[1]), 1)
			
			// second frame
			frame = m_top_config.m_spi_frame_subscriber.frames[1];	
			`FAIL_UNLESS_EQUAL(frame.commands.size(), 2)
			
			`FAIL_UNLESS_EQUAL($cast(pdcm_seq,frame.commands[0]), 1)
			`FAIL_UNLESS_EQUAL(pdcm_seq.channel_bits, 2'b11)
			`FAIL_UNLESS_EQUAL(pdcm_seq.pulse_count, 3)
						
			`FAIL_UNLESS_EQUAL($cast(crc_seq, frame.commands[1]), 1)
			`FAIL_UNLESS_EQUAL(crc_seq.get_word_count(), 2)
			`FAIL_UNLESS_EQUAL(crc_seq.mosi_crc_correct, 1)
			`FAIL_UNLESS_EQUAL(crc_seq.miso_crc_correct, 1)
		`SVTEST_END
		
		//=============================================================================

		`SVTEST ("spi_reset_command_tx_crc_calculation_test")
			spi_command_frame_seq frame = new();
			spi_write_master_register_seq write1_seq = new();
			spi_write_master_register_seq write2_seq = new();
			spi_tx_crc_request_seq crc1_seq = new();
			spi_tx_crc_request_seq crc2_seq = new();
			spi_reset_seq reset_seq = new();
			
			logging_spi_sequencer sequencer = m_top_config.m_sequencer;
	
			m_top_config.clear();
			`FAIL_IF_EQUAL(write1_seq.randomize() with {address == 12'h400; data == 16'h001c;}, 0)
			`FAIL_IF_EQUAL(crc1_seq.randomize() with { mosi_crc_correct == 1'b1;}, 0)
			crc1_seq.mosi_crc_enable = 1'b1;
			`FAIL_IF_EQUAL(write2_seq.randomize() with {address == 12'h400; data == 16'h001c;}, 0)
			`FAIL_IF_EQUAL(crc2_seq.randomize() with { mosi_crc_correct == 1'b1;}, 0)
			crc2_seq.mosi_crc_enable = 1'b1;
			`FAIL_IF_EQUAL(reset_seq.randomize(), 0)
			
			sequencer.data_out = {16'h0000, 16'h5400, 16'h00c, 16'h6267, 16'hFFFF, 16'hFFFF, 16'hFFFF, 16'h0000, 16'h5400, 16'h00c, 16'h6267};
			sequencer.m_config.csb_handler = per_frame_csb_hander::create();
			
			frame.set_sequencer(sequencer);
			frame.add_command(write1_seq);
			frame.add_command(crc1_seq);
			frame.add_command(reset_seq);
			frame.add_command(write2_seq);
			frame.add_command(crc2_seq);
	
			frame.body();
			
			`FAIL_UNLESS_EQUAL(sequencer.transactions.size(), 14)
			`FAIL_UNLESS_EQUAL(sequencer.transactions[0].tr_type, spi_pkg::SPI_START)
			`FAIL_UNLESS_EQUAL(sequencer.transactions[1].data_in, 16'h5400)
			`FAIL_UNLESS_EQUAL(sequencer.transactions[2].data_in, 16'h001c)
			`FAIL_UNLESS_EQUAL(sequencer.transactions[3].data_in, crc1_seq.get_word(0))
			`FAIL_UNLESS_EQUAL(sequencer.transactions[4].data_in, crc_calculation_pkg::spi_calculate_correct_crc({16'h5400, 16'h001c, crc1_seq.get_word(0)}))
			`FAIL_UNLESS_EQUAL(sequencer.transactions[5].data_in, reset_seq.get_word(0))
			`FAIL_UNLESS_EQUAL(sequencer.transactions[6].data_in, reset_seq.get_word(1))
			`FAIL_UNLESS_EQUAL(sequencer.transactions[7].data_in, reset_seq.get_word(2))
			`FAIL_UNLESS_EQUAL(sequencer.transactions[8].data_in, reset_seq.get_word(3))
			`FAIL_UNLESS_EQUAL(sequencer.transactions[9].data_in, 16'h5400)
			`FAIL_UNLESS_EQUAL(sequencer.transactions[10].data_in, 16'h001c)
			`FAIL_UNLESS_EQUAL(sequencer.transactions[11].data_in, crc2_seq.get_word(0))
			`FAIL_UNLESS_EQUAL(sequencer.transactions[12].data_in, crc_calculation_pkg::spi_calculate_correct_crc({16'h5400, 16'h001c, crc2_seq.get_word(0)}))
			`FAIL_UNLESS_EQUAL(sequencer.transactions[13].tr_type, spi_pkg::SPI_END)
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("spi_incomplete_read_pdcm_frame_both_channels_test")
			spi_read_pdcm_frame_seq read_seq = new();
			spi_tx_crc_request_seq crc_seq;
			spi_command_frame_seq frame;
			m_top_config.clear();
			
			set_tdma_scheme(2'b11, 300, {8}, {30}, {70});
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener,
					{16'h4c00, 16'h1000},
					{16'h0000, 16'h4c00});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_frame_subscriber.frames.size(), 1)
			frame = m_top_config.m_spi_frame_subscriber.frames[0];	
			`FAIL_UNLESS_EQUAL(frame.commands.size(), 2)
			
			`FAIL_UNLESS_EQUAL($cast(read_seq,	frame.commands[0]), 1)
			`FAIL_UNLESS_EQUAL($cast(crc_seq, 	frame.commands[1]), 1)
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("multiple_burst_reads_in_one_frame_test_small")
			spi_read_master_register_seq read1_seq, read2_seq;
			spi_tx_crc_request_seq crc_seq;
			spi_command_frame_seq frame;
			m_top_config.clear();
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
				//   <--------- read 1 ---------->  <-------- read 2 ---------->  <-- crc ---->
					{16'h2000, 16'h2122, 16'h2000, 16'h2000, 16'h2112, 16'h2000, 16'h137d},
					{16'hc417, 16'h2000, 16'h0582, 16'h0583, 16'h2000, 16'h0502, 16'h0503});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_frame_subscriber.frames.size(), 1)
			frame = m_top_config.m_spi_frame_subscriber.frames[0];	
			`FAIL_UNLESS_EQUAL(frame.commands.size(), 3)
			
			`FAIL_UNLESS_EQUAL($cast(read1_seq,	frame.commands[0]), 1)
			`FAIL_UNLESS_EQUAL($cast(read2_seq, frame.commands[1]), 1)
			`FAIL_UNLESS_EQUAL($cast(crc_seq,   frame.commands[2]), 1)
			
			`FAIL_UNLESS_EQUAL(read1_seq.address, 0)
			`FAIL_UNLESS_EQUAL(read1_seq.data, 16'h0582)
			`FAIL_UNLESS_EQUAL(read1_seq.burst_addresses.size(), 1)
			`FAIL_UNLESS_EQUAL(read1_seq.burst_addresses[0], 12'h122)
			`FAIL_UNLESS_EQUAL(read1_seq.burst_data.size(), 1)
			`FAIL_UNLESS_EQUAL(read1_seq.burst_data[0], 16'h0583)
			
			`FAIL_UNLESS_EQUAL(read2_seq.address, 0)
			`FAIL_UNLESS_EQUAL(read2_seq.data, 16'h0502)
			`FAIL_UNLESS_EQUAL(read2_seq.burst_addresses.size(), 1)
			`FAIL_UNLESS_EQUAL(read2_seq.burst_addresses[0], 12'h112)
			`FAIL_UNLESS_EQUAL(read2_seq.burst_data.size(), 1)
			`FAIL_UNLESS_EQUAL(read2_seq.burst_data[0], 16'h503)
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("multiple_burst_reads_in_one_frame_test")
			spi_read_master_register_seq read1_seq, read2_seq;
			spi_tx_crc_request_seq crc_seq;
			spi_command_frame_seq frame;
			m_top_config.clear();
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
				//   <----------------------------- read 1 ----------------------------->  <------------------- read 2 --------------------------------------->  <-- crc ---->
					{16'h2000, 16'h2122, 16'h2120, 16'h2128, 16'h212a, 16'h2129, 16'h2000, 16'h2000, 16'h2112, 16'h2110, 16'h2118, 16'h211a, 16'h2119, 16'h2000, 16'h137d},
					{16'hc417, 16'h2000, 16'h0000, 16'h007f, 16'h0000, 16'h0581, 16'h0582, 16'h0583, 16'h2000, 16'h0000, 16'h007f, 16'h0000, 16'h0501, 16'h0502, 16'h0503});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_frame_subscriber.frames.size(), 1)
			frame = m_top_config.m_spi_frame_subscriber.frames[0];	
			`FAIL_UNLESS_EQUAL(frame.commands.size(), 3)
			
			`FAIL_UNLESS_EQUAL($cast(read1_seq,	frame.commands[0]), 1)
			`FAIL_UNLESS_EQUAL($cast(read2_seq, frame.commands[1]), 1)
			`FAIL_UNLESS_EQUAL($cast(crc_seq,   frame.commands[2]), 1)
			
			`FAIL_UNLESS_EQUAL(read1_seq.address, 0)
			`FAIL_UNLESS_EQUAL(read1_seq.data, 0)
			`FAIL_UNLESS_EQUAL(read1_seq.burst_addresses.size(), 5)
			`FAIL_UNLESS_EQUAL(read1_seq.burst_addresses[0], 12'h122)
			`FAIL_UNLESS_EQUAL(read1_seq.burst_addresses[1], 12'h120)
			`FAIL_UNLESS_EQUAL(read1_seq.burst_addresses[2], 12'h128)
			`FAIL_UNLESS_EQUAL(read1_seq.burst_addresses[3], 12'h12a)
			`FAIL_UNLESS_EQUAL(read1_seq.burst_addresses[4], 12'h129)
			`FAIL_UNLESS_EQUAL(read1_seq.burst_data.size(), 5)
			`FAIL_UNLESS_EQUAL(read1_seq.burst_data[0], 16'h007f)
			`FAIL_UNLESS_EQUAL(read1_seq.burst_data[1], 16'h0000)
			`FAIL_UNLESS_EQUAL(read1_seq.burst_data[2], 16'h0581)
			`FAIL_UNLESS_EQUAL(read1_seq.burst_data[3], 16'h0582)
			`FAIL_UNLESS_EQUAL(read1_seq.burst_data[4], 16'h0583)
			
			`FAIL_UNLESS_EQUAL(read2_seq.address, 0)
			`FAIL_UNLESS_EQUAL(read2_seq.data, 0)
			`FAIL_UNLESS_EQUAL(read2_seq.burst_addresses.size(), 5)
			`FAIL_UNLESS_EQUAL(read2_seq.burst_addresses[0], 12'h112)
			`FAIL_UNLESS_EQUAL(read2_seq.burst_addresses[1], 12'h110)
			`FAIL_UNLESS_EQUAL(read2_seq.burst_addresses[2], 12'h118)
			`FAIL_UNLESS_EQUAL(read2_seq.burst_addresses[3], 12'h11a)
			`FAIL_UNLESS_EQUAL(read2_seq.burst_addresses[4], 12'h119)
			`FAIL_UNLESS_EQUAL(read2_seq.burst_data.size(), 5)
			`FAIL_UNLESS_EQUAL(read2_seq.burst_data[0], 16'h007f)
			`FAIL_UNLESS_EQUAL(read2_seq.burst_data[1], 16'h0000)
			`FAIL_UNLESS_EQUAL(read2_seq.burst_data[2], 16'h0501)
			`FAIL_UNLESS_EQUAL(read2_seq.burst_data[3], 16'h0502)
			`FAIL_UNLESS_EQUAL(read2_seq.burst_data[4], 16'h0503)
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("multiple_zero_address_register_reads_test")
			spi_read_master_register_seq read1_seq, read2_seq, read3_seq;
			spi_tx_crc_request_seq crc_seq;
			spi_command_frame_seq frame;
			m_top_config.clear();
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener, 	
					{16'h2000, 16'h2000, 16'h2000, 16'h2000, 16'h2000, 16'h2000, 16'h137d},
					{16'h0c00, 16'h2000, 16'h0001, 16'h2000, 16'h0002, 16'h2000, 16'h0003});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_frame_subscriber.frames.size(), 1)
			frame = m_top_config.m_spi_frame_subscriber.frames[0];	
			`FAIL_UNLESS_EQUAL(frame.commands.size(), 4)
			
			`FAIL_UNLESS_EQUAL($cast(read1_seq,	frame.commands[0]), 1)
			`FAIL_UNLESS_EQUAL($cast(read2_seq, frame.commands[1]), 1)
			`FAIL_UNLESS_EQUAL($cast(read3_seq, frame.commands[2]), 1)
			`FAIL_UNLESS_EQUAL($cast(crc_seq,   frame.commands[3]), 1)
			
			`FAIL_UNLESS_EQUAL(read1_seq.address, 0)
			`FAIL_UNLESS_EQUAL(read1_seq.data, 16'h0001)
			`FAIL_UNLESS_EQUAL(read1_seq.burst_addresses.size(), 0)
			`FAIL_UNLESS_EQUAL(read1_seq.burst_data.size(), 0)
			
			`FAIL_UNLESS_EQUAL(read2_seq.address, 0)
			`FAIL_UNLESS_EQUAL(read2_seq.data, 16'h0002)
			`FAIL_UNLESS_EQUAL(read2_seq.burst_addresses.size(), 0)
			`FAIL_UNLESS_EQUAL(read2_seq.burst_data.size(), 0)
			
			`FAIL_UNLESS_EQUAL(read3_seq.address, 0)
			`FAIL_UNLESS_EQUAL(read3_seq.data, 16'h0003)
			`FAIL_UNLESS_EQUAL(read3_seq.burst_addresses.size(), 0)
			`FAIL_UNLESS_EQUAL(read3_seq.burst_data.size(), 0)
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("spi_incomplete_reset_command_one_word_test")
			spi_crm_seq crm_seq;
			spi_reset_seq reset_seq;
			spi_tx_crc_request_seq crc_seq;
			spi_command_frame_seq frame;
			m_top_config.clear();
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener,
					{16'h8C00, 16'h915d, 16'hd5fe, 16'hffff, 16'h1000},
					{16'h0c00, 16'h8C00, 16'h915d, 16'hd5fe, 16'hffff});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_frame_subscriber.frames.size(), 1)
			frame = m_top_config.m_spi_frame_subscriber.frames[0];	
			`FAIL_UNLESS_EQUAL(frame.commands.size(), 3)
			
			`FAIL_UNLESS_EQUAL($cast(crm_seq,	frame.commands[0]), 1)
			`FAIL_UNLESS_EQUAL($cast(reset_seq, frame.commands[1]), 1)
			`FAIL_UNLESS_EQUAL(reset_seq.incomplete, 1'b1)
			`FAIL_UNLESS_EQUAL(reset_seq.incomplete_word_count, 1)
			`FAIL_UNLESS_EQUAL($cast(crc_seq, 	frame.commands[2]), 1)
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("spi_incomplete_reset_command_wrong_last_word_test")
			spi_crm_seq crm_seq;
			spi_reset_seq reset_seq;
			spi_tx_crc_request_seq crc_seq;
			spi_command_frame_seq frame;
			m_top_config.clear();
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener,
					{16'h8C00, 16'h915d, 16'hd5fe, 16'hffff, 16'hffff, 16'hffff, 16'hfffc, 16'h1000},
					{16'h0c00, 16'h8C00, 16'h915d, 16'hd5fe, 16'hffff, 16'hffff, 16'hffff, 16'hfffc});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_frame_subscriber.frames.size(), 1)
			frame = m_top_config.m_spi_frame_subscriber.frames[0];	
			`FAIL_UNLESS_EQUAL(frame.commands.size(), 3)
			
			`FAIL_UNLESS_EQUAL($cast(crm_seq,	frame.commands[0]), 1)
			`FAIL_UNLESS_EQUAL($cast(reset_seq, frame.commands[1]), 1)
			`FAIL_UNLESS_EQUAL(reset_seq.incomplete, 1'b1)
			`FAIL_UNLESS_EQUAL(reset_seq.incomplete_word_count, 4)
			`FAIL_UNLESS_EQUAL(reset_seq.get_word(0), 16'hffff)
			`FAIL_UNLESS_EQUAL(reset_seq.get_word(1), 16'hffff)
			`FAIL_UNLESS_EQUAL(reset_seq.get_word(2), 16'hffff)
			`FAIL_UNLESS_EQUAL(reset_seq.get_word(3), 16'hfffc)
			
			`FAIL_UNLESS_EQUAL($cast(crc_seq, 	frame.commands[2]), 1)
		`SVTEST_END

		 
		//=============================================================================
		
		`SVTEST ("spi_multiple_incomplete_reset_commands_test")
			spi_reset_seq reset_1_seq, reset_2_seq;
			spi_tx_crc_request_seq crc_seq;
			spi_command_frame_seq frame;
			m_top_config.clear();
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener,
					{16'hffff, 16'hfffc, 16'hffff, 16'hffff, 16'hffff, 16'h1000},
					{16'h0c00, 16'hffff, 16'hfffc, 16'hffff, 16'hffff, 16'hffff});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_frame_subscriber.frames.size(), 1)
			frame = m_top_config.m_spi_frame_subscriber.frames[0];	
			`FAIL_UNLESS_EQUAL(frame.commands.size(), 3)
			
			`FAIL_UNLESS_EQUAL($cast(reset_1_seq,	frame.commands[0]), 1)
			`FAIL_UNLESS_EQUAL(reset_1_seq.incomplete, 1'b1)
			`FAIL_UNLESS_EQUAL(reset_1_seq.incomplete_word_count, 2)
			`FAIL_UNLESS_EQUAL(reset_1_seq.get_word(0), 16'hffff)
			`FAIL_UNLESS_EQUAL(reset_1_seq.get_word(1), 16'hfffc)
			
			`FAIL_UNLESS_EQUAL($cast(reset_2_seq, frame.commands[1]), 1)
			`FAIL_UNLESS_EQUAL(reset_2_seq.incomplete, 1'b1)
			`FAIL_UNLESS_EQUAL(reset_2_seq.incomplete_word_count, 3)
			`FAIL_UNLESS_EQUAL(reset_2_seq.get_word(0), 16'hffff)
			`FAIL_UNLESS_EQUAL(reset_2_seq.get_word(1), 16'hffff)
			`FAIL_UNLESS_EQUAL(reset_2_seq.get_word(2), 16'hffff)
			
			`FAIL_UNLESS_EQUAL($cast(crc_seq, 	frame.commands[2]), 1)
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("spi_multiple_reset_commands_test")
			spi_reset_seq reset_1_seq, reset_2_seq;
			spi_tx_crc_request_seq crc_seq;
			spi_command_frame_seq frame1, frame2, frame3;
			m_top_config.clear();
			
			send_spi_tr_with_crc(m_top_config.m_spi_protocol_listener,
					{16'hFFFF, 16'hFFFF, 16'hFFFF, 16'hFFFE, 16'hFFFF, 16'hFFFF, 16'hFFFF, 16'hFFFE, 16'h1000},
					{16'h0c00, 16'hFFFF, 16'hFFFF, 16'hFFFF, 16'hFFFE, 16'hFFFF, 16'hFFFF, 16'hFFFF, 16'hFFFE});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_frame_subscriber.frames.size(), 3)
			
			frame1 = m_top_config.m_spi_frame_subscriber.frames[0];	
			`FAIL_UNLESS_EQUAL(frame1.commands.size(), 1)
			`FAIL_UNLESS_EQUAL($cast(reset_1_seq, frame1.commands[0]), 1)
			`FAIL_UNLESS_EQUAL(reset_1_seq.incomplete, 1'b0)
			
			frame2 = m_top_config.m_spi_frame_subscriber.frames[1];	
			`FAIL_UNLESS_EQUAL(frame2.commands.size(), 1)
			`FAIL_UNLESS_EQUAL($cast(reset_2_seq, frame2.commands[0]), 1)
			`FAIL_UNLESS_EQUAL(reset_2_seq.incomplete, 1'b0)
			
			frame3 = m_top_config.m_spi_frame_subscriber.frames[2];	
			`FAIL_UNLESS_EQUAL(frame3.commands.size(), 1)
			`FAIL_UNLESS_EQUAL($cast(crc_seq, 	frame3.commands[0]), 1)
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("spi_incomplete_crm_read_followed_by_reset_command_test")
			spi_reset_seq reset_seq;
			spi_read_crm_data_packets_seq read_seq;
			spi_command_frame_seq frame;
			m_top_config.clear();
			
			send_spi_tr(m_top_config.m_spi_protocol_listener,
					{16'h37b6, 16'h3361, 16'h3bxx, 16'hffff, 16'hffff, 16'hffff, 16'hfffe},
					{16'h0c01, 16'h37b6, 16'h00xx, 16'h2715, 16'hffff, 16'hffff, 16'hffff});
			
			`FAIL_UNLESS_EQUAL(m_top_config.m_spi_frame_subscriber.frames.size(), 1)
			
			frame = m_top_config.m_spi_frame_subscriber.frames[0];	
			`FAIL_UNLESS_EQUAL(frame.commands.size(), 2)
			`FAIL_UNLESS_EQUAL($cast(read_seq,  frame.commands[0]), 1)
			`FAIL_UNLESS_EQUAL(read_seq.incomplete, 1'b1)
			`FAIL_UNLESS_EQUAL(read_seq.incomplete_word_count, 3)
			`FAIL_UNLESS_EQUAL(read_seq.get_word_count(), 3)
			`FAIL_UNLESS_EQUAL(read_seq.get_data_packet(0).data.size(), 1)
			`FAIL_UNLESS_EQUAL(read_seq.get_data_packet(0).data[0], 16'h2715)
			
			`FAIL_UNLESS_EQUAL($cast(reset_seq, frame.commands[1]), 1)
			`FAIL_UNLESS_EQUAL(reset_seq.incomplete, 1'b0)
		`SVTEST_END
		 
	`SVUNIT_TESTS_END
	
	task check_data_packet( spi_dsi_data_packet packet, logic[1:0] channel_index, logic[7:0] symbol_count, logic[15:0] data[$]);
		`FAIL_UNLESS_EQUAL(packet.channel_index, channel_index)
		`FAIL_UNLESS_EQUAL(packet.symbol_count, symbol_count)
		`FAIL_UNLESS_EQUAL(packet.data.size(), data.size())
		foreach(data[i]) begin		
			`FAIL_UNLESS_EQUAL(packet.data[i], data[i])
		end
	endtask
		
endmodule
