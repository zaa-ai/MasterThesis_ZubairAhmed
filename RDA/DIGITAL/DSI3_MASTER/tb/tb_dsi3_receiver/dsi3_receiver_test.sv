`include "svunit_defines.svh"

module dsi3_receiver_test import project_pkg::*; ();
	
	`include "uvm_macros.svh"
	
	import svunit_pkg::svunit_testcase;
	import svunit_uvm_mock_pkg::*;
	import addresses_pkg::*;
	import common_test_pkg::*;
	import dsi3_slave_pkg::*;
	import uvm_pkg::*;
	import unit_test_pkg::*;
	import common_env_pkg::*;
	import dsi3_pkg::*;

	string name = "dsi3_receiver_test";
	svunit_testcase svunit_ut;
	
	//===================================
	// This is the UUT that we're 
	// running the Unit Tests on
	//===================================
	dsi3_slave_agent		slave_agent;
	dsi3_slave_sequencer_t	slave_sequencer;
	dsi3_slave_seq			slave_seq[$];
	receive_service			_receive;
	top_config				_top_config;
	dsi3_slave_if			slave_if();
    `ifdef DO_EXHAUSTIVE_RECEIVER_TESTS
	timing_container	 	stc;
	slave_timing_selector	current_selector;
    `endif
	
	l4_queue test_data[$];
	initial begin
		l4_queue temp;
		test_data.delete();
		void'(convert_queue #(12, 4)::convert('{12'h2c3}, temp));
		test_data.push_back(temp);
        void'(convert_queue #(16, 4)::convert('{16'hc101}, temp));
		test_data.push_back(temp);
        void'(convert_queue #(36, 4)::convert('{36'hbce3_7a11_a}, temp));
		test_data.push_back(temp);
		
        void'(convert_queue #(32, 4)::convert('{32'h3e13_a4b6},temp));
		test_data.push_back(temp);
        void'(convert_queue #(32, 4)::convert('{32'h1090_8398},temp));
		test_data.push_back(temp);
        void'(convert_queue #(32, 4)::convert('{32'h2f1a_f3ac},temp));
		test_data.push_back(temp);
		
		
		//random
		temp.delete();
		repeat($urandom_range(128,255))
			temp.push_back($urandom_range(0,15));
		test_data.push_back(temp);
		
		// from JIRA C52142-108
        void'(convert_queue #(32, 4)::convert('{32'habf3_7aba},temp));
		test_data.push_back(temp);
	end
	
	`clk_def(27777ps)
	
	`tick_gen
	
	initial begin
		_top_config = new("_top_config");
		
		uvm_config_db #(top_config)::set(null, "uvm_test_top", "_top_config", _top_config);
		uvm_config_db #(top_config)::set(null, "uvm_test_top.m_env", "_top_config", _top_config);
		_top_config._dsi3_slave_config.vif	= slave_if;   
				
		run_test();
	end
	
	logic[15:0] time_base;
	initial begin
		time_base = '0;
		forever begin
			@(posedge tick_1us);
			if (tick_1us == 1'b1)
				time_base+=16'd1;
		end
	end
	
	logic enable, received_data, response_finished, SYMBOL_ERROR, symbol_count_over_flow;
	logic[1:0]	i_dsi3_in;
	data_ecc_t	rx_data;
	logic[8:0]	symbol_count;
	
	logic	o_receiving_started_tick, o_received_c0_after_packet;
	logic[1:0]	o_rx_filtered;
	
	real	load;
	initial begin
		enable = 1'b0;
		common_config.chip_time = CHIPTIME_2US;
		i_dsi3_in = '0;
	end
	
	logic	o_rec_pending, o_symbol_error_set_for_mon;
	data_t	receive_time_out;
	logic	receive_time_out_tick;
	assign	receive_time_out_tick = (receive_time_out == time_base) ? tick_1us : 1'b0; 
	dsi3_common_config_if common_config ();
	
	dsi3_receive i_dsi3_receive (
		.clk_rst              (clk_rst.slave       ), 
		.i_enable_receiver    (enable              ), 
		.i_rx                 (i_dsi3_in           ), 
		.i_sample_cfg         (common_config.chip_time ),
		.i_receive_time_out   (receive_time_out_tick),
		.o_rec_pending        (o_rec_pending       ), 
		.o_symbol_error_set   (o_symbol_error_set_for_mon), 
		.o_response_finished  (response_finished   ),
		.o_received_data      (received_data       ),
		.o_data               (rx_data             ),
		.o_symbol_count       (symbol_count        ),
		.o_symbol_count_overflow(symbol_count_over_flow),
		.o_rx_test                 (                          ),
		.o_rx_filtered             (o_rx_filtered             ),
		.o_receiving_started_tick  (o_receiving_started_tick  ),
		.o_received_c0_after_packet(o_received_c0_after_packet)
	);
	
	always@(slave_if.cable.Current) begin
		i_dsi3_in[0] = (slave_if.cable.Current > 0) ? 1'b1 : 1'b0;
		i_dsi3_in[1] = (slave_if.cable.Current > 1) ? 1'b1 : 1'b0;
	end
	
	always@(posedge received_data) begin
		@(posedge clk_rst.clk);
		if (received_data == 1'b1) begin
			_receive.receive_data(rx_data.data);
		end
	end
	
	always@(posedge response_finished) begin
		@(posedge clk_rst.clk);
		if (response_finished == 1'b1) begin
			_receive.finish(symbol_count_over_flow, symbol_count);
		end
	end
	
	always@(posedge o_symbol_error_set_for_mon) begin
		SYMBOL_ERROR = 1'b1;
	end
	
	//===================================
	// Build
	//===================================
	function void build();
		svunit_ut = new(name);
		_receive = new();
	endfunction

	//===================================
	// Setup for running the Unit Tests
	//===================================
	task setup();
		svunit_ut.setup();
		
		SYMBOL_ERROR = 1'b0;
		_receive.initialize();
		slave_if.cable.Current = 0;
		common_config.chip_time = CHIPTIME_2US;
		uvm_report_mock::setup();
		
		receive_time_out = time_base - 16'd2;
		enable = 1'b1;
		set_mode(MODE_PDCM);
		#1us;
	endtask

	//===================================
	// Here we deconstruct anything we 
	// need after running the Unit Tests
	//===================================
	task teardown();
		svunit_ut.teardown();
		
		enable = 1'b0;
		slave_if.cable.Current = 0;
		#1us;
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
	
	localparam time time_until_response_received = 20us;
	
	function void set_slave_test_sequences();
		
	endfunction
	
	function void set_mode(channel_mode_t new_mode);
		_receive.mode = new_mode;
	endfunction
			
	function void set_tolerance(dsi3_slave_seq seq, int tol_int);
		seq.req.tolerance_int = tol_int;
		seq.req.tolerance = (real'(tol_int)/1000.0);
	endfunction
	
	`SVUNIT_TESTS_BEGIN
	begin
		int receiver_selection = 1;
		enable_clk = 1'b1;
		#10us;
		slave_sequencer = _top_config._dsi3_slave_agent.m_sequencer;
		slave_agent = _top_config._dsi3_slave_agent;

			`SVTEST($sformatf("Test for iload of receiver %1d", receiver_selection))
				l4_queue temp;
				dsi3_slave_seq seq;
                void'(convert_queue #(352, 4)::convert('{352'h110100F0FFF0BFF0A7F0FFF0FFF0EAF0FFF0FFF0FFF0FFF0FFF0FFF0FFF0FFF0FFF0FFF0FFF0FFF0FFF0FF6D}, temp));
				seq = dsi3_receiver_test_slave_sequence::create_test_seq_with_data(slave_sequencer, temp);
				seq.start(slave_sequencer);
				#10us;
				seq.start(slave_sequencer);
				#10us;
			`SVTEST_END
			
			for (int loop=0; loop<10; loop++) begin
				`SVTEST($sformatf("%3d: Test for P52143-413 of receiver %1d with correct chip time", loop, receiver_selection))
					common_config.chip_time = CHIPTIME_3US;
					#1us;
		
					send_p52143_413_response();
					#40us;
					`FAIL_UNLESS_EQUAL(_receive.recfin_counter, 1);
				`SVTEST_END
			end
				
			for (int loop=0; loop<10; loop++) begin
				`SVTEST($sformatf("%3d: Test for P52143-413 of receiver %1d", loop, receiver_selection))
					common_config.chip_time = CHIPTIME_4US;
					#1us;
	
					send_p52143_413_response();
					#40us;
					`FAIL_UNLESS_EQUAL(_receive.recfin_counter, 1);
				`SVTEST_END
			end
				
			`SVTEST($sformatf("Check receive timeout of receiver when NOT receiving %1d", receiver_selection))
				bit received_timeout=1'b0;
				receive_time_out = time_base + 16'd4;
				fork
					begin
						#5us;
					end
					begin
						@(posedge response_finished);
						received_timeout=1'b1;
					end
				join_any
				disable fork;
				`FAIL_IF(!uvm_report_mock::verify_complete());
				`FAIL_UNLESS_EQUAL(received_timeout, 1'b0)
			`SVTEST_END
				
			`SVTEST($sformatf("Check receive timeout of receiver when receiving %1d", receiver_selection)) // FIXME: check test case!!!! seems not to work properly
				bit received_timeout=1'b0;
				time start_time, recto_time;
				receive_time_out = time_base + 16'd10;
				start_time = $time();
				fork
					begin
						slave_seq.push_back(dsi3_receiver_test_slave_sequence::create_test_seq(slave_sequencer));
						slave_seq[0].start(slave_sequencer);
						#(time_until_response_received);
					end
					begin
						@(posedge response_finished);
						received_timeout=1'b1;
						recto_time = $time();
						#100us;
					end
				join_any
				disable fork;
				`FAIL_IF(!uvm_report_mock::verify_complete());
				`FAIL_UNLESS_EQUAL(received_timeout, 1'b1)
			`SVTEST_END
			
			`SVTEST ($sformatf("eins of receiver %1d", receiver_selection))
				slave_seq.push_back(dsi3_receiver_test_slave_sequence::create_test_seq(slave_sequencer));
				slave_seq[0].start(slave_sequencer);
				#(time_until_response_received);
                void'(_receive.compare_response(slave_seq[0]));
				`FAIL_IF(!uvm_report_mock::verify_complete());
//				`FAIL_UNLESS (_receive.compare(slave_seq[0]))
			`SVTEST_END
		
			for(int symbols=1; symbols<12; symbols++) begin
				chipt_time_iterator_for_unit_tests chip_time_iterator;
				chip_time_iterator = new(common_config);
				while (chip_time_iterator.has_next()) begin
					int current_chip_time = chip_time_iterator.chip_time;
				   `SVTEST ($sformatf("symbol count not/ dividable by 4 (symbols:%1d) with %2dus chip time of receiver %1d", symbols, current_chip_time, receiver_selection))
						dsi3_slave_seq seq = dsi3_receiver_test_slave_sequence::create_test_seq(slave_sequencer, .symbol_count(symbols), .chiptime(current_chip_time));
					   chip_time_iterator.apply_next();
						seq.start(slave_sequencer);
						#(time_until_response_received*current_chip_time/3);
                        void'(_receive.compare_response(seq));
						`FAIL_IF(!uvm_report_mock::verify_complete());
						`FAIL_UNLESS_EQUAL(o_rec_pending, 1'b0)
				   `SVTEST_END
			   end
			end
			
			`SVTEST ($sformatf("symbol count overflow of receiver %1d", receiver_selection))
				dsi3_slave_seq seq = dsi3_receiver_test_slave_sequence::create_test_seq(slave_sequencer, .symbol_count(256));
				seq.start(slave_sequencer);
				#(time_until_response_received);
				`FAIL_IF(!uvm_report_mock::verify_complete());
				`FAIL_UNLESS_EQUAL(symbol_count, 9'h100)
				`FAIL_UNLESS_EQUAL(symbol_count_over_flow, 1'b1)
			`SVTEST_END
		
			`SVTEST ($sformatf("enable=0 does not reset symbol_count, received_data and symbol_count_overflow of receiver %1d", receiver_selection))
				l16	rec_data;
				logic[8:0] symb_cnt;
				logic	symb_ov;
				dsi3_slave_seq seq = dsi3_receiver_test_slave_sequence::create_test_seq(slave_sequencer);
				seq.start(slave_sequencer);
				#10us;
				symb_cnt = symbol_count;
				rec_data = rx_data.data;
				symb_ov = symbol_count_over_flow;
				enable = 1'b0;
				wait_for_n_clocks(3);
				`FAIL_UNLESS_EQUAL(rec_data, rx_data.data)
				`FAIL_UNLESS_EQUAL(symb_cnt, symbol_count);
				`FAIL_UNLESS_EQUAL(symb_ov, symbol_count_over_flow);
				#(time_until_response_received);
			`SVTEST_END
		
			`SVTEST($sformatf("Update data after reception of first word only of receiver %1d", receiver_selection))
				l16	rec_data_saved, rec_data_early, rec_data_late;
				dsi3_slave_seq seq = dsi3_receiver_test_slave_sequence::create_test_seq(slave_sequencer);
				seq.start(slave_sequencer);
				#(time_until_response_received);
				rec_data_saved = rx_data.data;
				fork
					begin
						seq = dsi3_receiver_test_slave_sequence::create_test_seq(slave_sequencer);
						seq.start(slave_sequencer);
						#(time_until_response_received);
					end
					begin
						#3.5us;
						rec_data_early = rx_data.data;
						#20us; // wait for less than 4 symbols * 3 chips/symbol * 3us/chip = 36us
						rec_data_late = rx_data.data;
					end
				join
				`FAIL_UNLESS_EQUAL (rec_data_early, rec_data_saved)
				`FAIL_UNLESS_EQUAL (rec_data_late, rec_data_saved)
			`SVTEST_END
			
//			`SVTEST($sformatf("Update SYMB_CNT after reception of first word only of receiver %1d", receiver_selection))
//				logic[8:0] symb_cnt_saved, symb_cnt_early, symb_cnt_late;
//				dsi3_slave_seq seq = dsi3_receiver_test_slave_sequence::create_test_seq(slave_sequencer);
//				seq.start(slave_sequencer);
//				#10us;
//				symb_cnt_saved = symbol_count;
//				fork
//					begin
//						seq = dsi3_receiver_test_slave_sequence::create_test_seq(slave_sequencer);
//						seq.start(slave_sequencer);
//						#10us;
//					end
//					begin
//						#3.5us;
//						symb_cnt_early = symbol_count;
//						#20us; // wait for less than 4 symbols * 3 chips/symbol * 3us/chip = 36us
//						symb_cnt_late = symbol_count;
//					end
//				join
//				`FAIL_UNLESS_EQUAL (symb_cnt_early, symb_cnt_saved)
//				`FAIL_UNLESS_EQUAL (symb_cnt_late, symb_cnt_saved)
//			`SVTEST_END
			
			`SVTEST($sformatf("Update data after reception of packet of receiver %1d", receiver_selection))
				l16	rec_data_saved, rec_data_early, rec_data_late;
				dsi3_slave_seq seq = dsi3_receiver_test_slave_sequence::create_test_seq(slave_sequencer);
				seq.start(slave_sequencer);
				#(time_until_response_received);
				rec_data_saved = rx_data.data;
				seq = dsi3_receiver_test_slave_sequence::create_test_seq(slave_sequencer, .symbol_count(4), .chiptime(3));
				common_config.chip_time = CHIPTIME_3US;
				fork
					begin
						seq.start(slave_sequencer);
					end
					begin
						#34us;
						rec_data_early = rx_data.data;
					end
				join
				#(time_until_response_received);
				rec_data_late = rx_data.data;
				`FAIL_UNLESS_EQUAL (rec_data_early, rec_data_saved)
				`FAIL_UNLESS (rec_data_late != rec_data_saved)
				`FAIL_IF_EQUAL(rec_data_late, rec_data_saved)
			`SVTEST_END
			
			`SVTEST($sformatf("Update symbol count after reception of packet of receiver %1d", receiver_selection))
				logic[8:0] symb_cnt_saved, symb_cnt_early, symb_cnt_late;
				dsi3_slave_seq seq = dsi3_receiver_test_slave_sequence::create_test_seq(slave_sequencer);
				seq.start(slave_sequencer);
				#(time_until_response_received);
				symb_cnt_saved = symbol_count;
				seq = dsi3_receiver_test_slave_sequence::create_test_seq(slave_sequencer, .symbol_count(4), .chiptime(3));
				common_config.chip_time = CHIPTIME_3US;
				fork
					seq.start(slave_sequencer);
					begin
						#34us;
						symb_cnt_early = symbol_count;
					end
				join
				#(time_until_response_received);
				symb_cnt_late = symbol_count;
				`FAIL_UNLESS_EQUAL (symb_cnt_early, symb_cnt_saved)
				`FAIL_UNLESS (symb_cnt_late != symb_cnt_saved)		
			`SVTEST_END
			
			`SVTEST($sformatf("Check several packets of receiver %1d", receiver_selection))
				dsi3_slave_seq seq;
				repeat (5) begin
					seq = dsi3_receiver_test_slave_sequence::create_test_seq(slave_sequencer, .symbol_count($urandom_range(4,1)*4));
					seq.start(slave_sequencer);
					#(time_until_response_received);
                    void'(_receive.compare_response(seq));
					`FAIL_IF(!uvm_report_mock::verify_complete());
					_receive.initialize();
				end
			`SVTEST_END	
			
			begin
				dsi3_slave_seq seq;
				int test_tolerance[$] = '{950, 1000, 1050};
				foreach (test_data[i]) begin
					foreach (test_tolerance[j]) begin
						chipt_time_iterator_for_unit_tests chip_time_iterator;
						chip_time_iterator = new(common_config);
						while (chip_time_iterator.has_next()) begin
							int current_chip_time = chip_time_iterator.chip_time;
							`SVTEST($sformatf("Check critical sequence %1d with tolerance %3d and chiptime %1dus of receiver %1d", i, test_tolerance[j]/10, current_chip_time, receiver_selection))
								seq = dsi3_receiver_test_slave_sequence::create_test_seq_with_data(slave_sequencer, test_data[i], current_chip_time);
								set_tolerance(seq, test_tolerance[j]);
								chip_time_iterator.apply_next();
								seq.start(slave_sequencer);
								#(current_chip_time*1us*5+1us);	//5 chips + 1µs filter time
                                void'(_receive.compare_response(seq));
								`FAIL_IF(!uvm_report_mock::verify_complete());
								_receive.initialize();						
							`SVTEST_END
						end
					end
				end
			end
			
			begin 
				chipt_time_iterator_for_unit_tests chip_time_iterator;
				chip_time_iterator = new(common_config);
				while (chip_time_iterator.has_next()) begin
					dsi3_slave_seq seq, seq_disturb;
					int current_chip_time = chip_time_iterator.chip_time;
					`SVTEST($sformatf("Receive disturbances of less than a third of a chip (c100) and chiptime=%1dus of receiver %1d", current_chip_time, receiver_selection))
						chip_time_iterator.apply_current();
						seq_disturb = dsi3_receiver_test_slave_sequence::create_test_seq_with_data(slave_sequencer, '{4'h4}, current_chip_time);
						seq = dsi3_receiver_test_slave_sequence::create_test_seq_with_data(slave_sequencer, test_data[3], current_chip_time);
						#10us;
						set_tolerance(seq_disturb, 330);
						seq_disturb.start(slave_sequencer);
						#10us;
						seq.start(slave_sequencer);
						#(time_until_response_received*current_chip_time/3);
                        void'(_receive.compare_response(seq));
						`FAIL_IF(!uvm_report_mock::verify_complete());
					`SVTEST_END
					
					`SVTEST($sformatf("Receive disturbances of less than a third of a chip (c200) and chiptime=%1dus of receiver %1d", current_chip_time, receiver_selection))
						chip_time_iterator.apply_current();
						seq_disturb = dsi3_receiver_test_slave_sequence::create_test_seq_with_data(slave_sequencer, '{4'hd}, current_chip_time);
						seq = dsi3_receiver_test_slave_sequence::create_test_seq_with_data(slave_sequencer, test_data[3], current_chip_time);
						#10us;
						set_tolerance(seq_disturb, 330);
						seq_disturb.start(slave_sequencer);
						#10us;
						seq.start(slave_sequencer);
						#(time_until_response_received*current_chip_time/3);
                        void'(_receive.compare_response(seq));
						`FAIL_IF(!uvm_report_mock::verify_complete());
					`SVTEST_END
				
					`SVTEST($sformatf("Receive disturbances of less than a third of a chip (c100) and chiptime=%1dus in PDCM of receiver %1d", current_chip_time, receiver_selection))
						chip_time_iterator.apply_current();
						seq_disturb = dsi3_receiver_test_slave_sequence::create_test_seq_with_data(slave_sequencer, '{4'h4}, current_chip_time);
						seq = dsi3_receiver_test_slave_sequence::create_test_seq_with_data(slave_sequencer, test_data[3], current_chip_time);
						#10us;
						seq.start(slave_sequencer);
						#(time_until_response_received*current_chip_time/3);
						`FAIL_UNLESS (_receive.compare_response(seq))
						_receive.initialize();
						set_tolerance(seq_disturb, 350);
						seq_disturb.start(slave_sequencer);
						#10us;
						seq.start(slave_sequencer);
						#(time_until_response_received*current_chip_time/3);
                        void'(_receive.compare_response(seq));
						`FAIL_IF(!uvm_report_mock::verify_complete());
					`SVTEST_END
				
					`SVTEST($sformatf("Receive disturbances of less than a third of a chip (c200) and chiptime=%1dus in PDCM of receiver %1d", current_chip_time, receiver_selection))
						chip_time_iterator.apply_current();
						seq_disturb = dsi3_receiver_test_slave_sequence::create_test_seq_with_data(slave_sequencer, '{4'hd}, current_chip_time);
						seq = dsi3_receiver_test_slave_sequence::create_test_seq_with_data(slave_sequencer, test_data[3], current_chip_time);
						#10us;
						seq.start(slave_sequencer);
						#(time_until_response_received*current_chip_time/3);
						`FAIL_UNLESS (_receive.compare_response(seq))
						_receive.initialize();
						set_tolerance(seq_disturb, 330);
						seq_disturb.start(slave_sequencer);
						#10us;
						seq.start(slave_sequencer);
						#(time_until_response_received*current_chip_time/3);
                        void'(_receive.compare_response(seq));
						`FAIL_IF(!uvm_report_mock::verify_complete());
					`SVTEST_END
					chip_time_iterator.apply_next();
				end
			end
			
			
			`SVTEST($sformatf("SYMBCNT updated at RECTO IRQ (C52142-107) of receiver %1d", receiver_selection))
				dsi3_slave_seq seq = dsi3_receiver_test_slave_sequence::create_test_seq(slave_sequencer, .symbol_count(8), .chiptime(3));
				common_config.chip_time = CHIPTIME_3US;
				receive_time_out = time_base+16'd70;
				fork
					begin
						seq.start(slave_sequencer);
						#10us;
					end
					begin
						@(posedge response_finished);
						wait_for_n_clocks(1);
						#10ns enable = 1'b0;
					end
				join
                void'(seq.packet.data.pop_back());
				`FAIL_UNLESS_EQUAL(symbol_count, 7)
                void'(_receive.compare_response(seq));
				`FAIL_IF(!uvm_report_mock::verify_complete());
			`SVTEST_END
				
			`SVTEST($sformatf("SYMBCNT updated at RECTO IRQ (C52142-107) of receiver %1d other test", receiver_selection))
				dsi3_slave_seq seq = dsi3_receiver_test_slave_sequence::create_test_seq(slave_sequencer, .symbol_count(8), .chiptime(3));
				receive_time_out = time_base+16'd70;
				common_config.chip_time = CHIPTIME_3US;
				fork
					begin
						seq.start(slave_sequencer);
						#10us;
					end
					begin
						@(posedge response_finished);
						wait_for_n_clocks(1);
						#10ns enable = 1'b0;
					end
				join
                void'(seq.packet.data.pop_back());
				`FAIL_UNLESS_EQUAL(symbol_count, 7)
                void'(_receive.compare_response(seq));
				`FAIL_IF(!uvm_report_mock::verify_complete());
			`SVTEST_END
				
			`SVTEST($sformatf("REC_DATA updated at RECTO IRQ (C52142-107) of receiver %1d", receiver_selection))
				dsi3_slave_seq seq = dsi3_receiver_test_slave_sequence::create_test_seq(slave_sequencer, .symbol_count(8), .chiptime(3));
				common_config.chip_time = CHIPTIME_3US;
				receive_time_out = time_base+16'd70;
				fork
					begin
						seq.start(slave_sequencer);
						#10us;
					end
					begin
						@(posedge response_finished);
						wait_for_n_clocks(1);
						#10ns enable = 1'b0;
					end
				join
                void'(seq.packet.data.pop_back());
                void'(_receive.compare_response(seq));
				`FAIL_IF(!uvm_report_mock::verify_complete());
			`SVTEST_END
				
			`SVTEST($sformatf("REC_DATA correctly after RECTO IRQ of receiver %1d", receiver_selection))
				l16_queue words;
				l16 register_data, packet_data;
				
				dsi3_slave_seq seq = dsi3_receiver_test_slave_sequence::create_test_seq(slave_sequencer, .symbol_count(7));
				receive_time_out = time_base+16'd75;
				fork
					begin
						seq.start(slave_sequencer);
						#10us;
					end
					begin
						@(posedge response_finished);
						wait_for_n_clocks(1);
						#10ns enable = 1'b0;
					end
				join
				register_data = rx_data.data;
                void'(convert_queue #(4, 16)::convert(seq.packet.data, words));
				packet_data = words[1];
				foreach (packet_data[i]) begin
					if (packet_data[i] === 1'bx)
						packet_data[i] = 1'b0;
				end
				
				`FAIL_UNLESS_EQUAL(packet_data, register_data)
                void'(_receive.compare_response(seq));
				`FAIL_IF(!uvm_report_mock::verify_complete());
				
			`SVTEST_END
			
			`SVTEST($sformatf("REC_FIN when symbol error occurs in last symbol(C52142-506) of receiver %1d", receiver_selection))
				l4_queue queue_of_nibbles;
				dsi3_pkg::dsi3_symbol symbols[$];
				dsi3_slave_seq seq;
				dsi3_packet packet;
				
                void'(convert_queue #(32, 4)::convert('{32'hf29e_77bf},queue_of_nibbles));
				seq = dsi3_receiver_test_slave_sequence::create_test_seq_with_data(slave_sequencer, queue_of_nibbles);

				create_queue_of_symbols(queue_of_nibbles, symbols);
				symbols[$] = dsi3_pkg::dsi3_symbol'({dsi3_pkg::C1, dsi3_pkg::C1, dsi3_pkg::C1});
				while (symbols.size()>0) begin
					send_symbol(symbols.pop_front());
				end
				send_symbol(dsi3_pkg::dsi3_symbol'({dsi3_pkg::C0, dsi3_pkg::C0, dsi3_pkg::C0}));
				
				$cast(packet, seq.packet);
				// change content due to symbol coding error -> (wrong CRC -> sourceID cannot automatically retrieved from content) + data[7]=0 
				packet.data[7] = 4'h0;
				packet.crc_correct = 1'b0;
				
				#(time_until_response_received);
				`FAIL_UNLESS_EQUAL(SYMBOL_ERROR, 1'b1)
                void'(_receive.compare_response(seq));
				`FAIL_IF(!uvm_report_mock::verify_complete());
			`SVTEST_END
				
			`SVTEST($sformatf("Packet with symbol coding error in first symbol of receiver %1d", receiver_selection))
				l4_queue queue_of_nibbles;
				dsi3_pkg::dsi3_symbol symbols[$];
				dsi3_slave_seq seq;
				dsi3_packet packet;
				
                void'(convert_queue #(32, 4)::convert('{32'hf29e_77bf},queue_of_nibbles));
				seq = dsi3_receiver_test_slave_sequence::create_test_seq_with_data(slave_sequencer, queue_of_nibbles);

				create_queue_of_symbols(queue_of_nibbles, symbols);
				symbols[0] = dsi3_pkg::dsi3_symbol'({dsi3_pkg::C1, dsi3_pkg::C1, dsi3_pkg::C1});
				while (symbols.size()>0) begin
					send_symbol(symbols.pop_front());
				end
				send_symbol(dsi3_pkg::dsi3_symbol'({dsi3_pkg::C0, dsi3_pkg::C0, dsi3_pkg::C0}));
				
				$cast(packet, seq.packet);
				// change content due to symbol coding error -> (wrong CRC -> sourceID cannot automatically retrieved from content) + data[7]=0 
				packet.data[0] = 4'h0;
				packet.crc_correct = 1'b0;
				
				#(time_until_response_received);
				`FAIL_UNLESS_EQUAL(SYMBOL_ERROR, 1'b1)
                void'(_receive.compare_response(seq));
				`FAIL_IF(!uvm_report_mock::verify_complete());
			`SVTEST_END
				
			`SVTEST($sformatf("Packet with symbol coding error in first symbol and only 1 symbol sent (BDM) of receiver %1d", receiver_selection))
				l4_queue queue_of_nibbles;
				dsi3_pkg::dsi3_symbol symbols[$];
				dsi3_slave_seq seq;
				dsi3_packet packet;
				
				queue_of_nibbles.push_back(4'h0);
				seq = dsi3_receiver_test_slave_sequence::create_test_seq_with_data(slave_sequencer, queue_of_nibbles);

				create_queue_of_symbols(queue_of_nibbles, symbols);
				symbols[0] = dsi3_pkg::dsi3_symbol'({dsi3_pkg::C1, dsi3_pkg::C1, dsi3_pkg::C1});
				while (symbols.size()>0) begin
					send_symbol(symbols.pop_front());
				end
				send_symbol(dsi3_pkg::dsi3_symbol'({dsi3_pkg::C0, dsi3_pkg::C0, dsi3_pkg::C0}));
				
				$cast(packet, seq.packet);
				// change content due to symbol coding error -> (wrong CRC -> sourceID cannot automatically retrieved from content) 
				packet.data[0] = 4'h0;
				packet.crc_correct = 1'b1; // is correct since CRC does not change when data is 0
				
				#(time_until_response_received);
				`FAIL_UNLESS_EQUAL(SYMBOL_ERROR, 1'b1)
                void'(_receive.compare_response(seq));
				`FAIL_IF(!uvm_report_mock::verify_complete());
			`SVTEST_END
			
			`SVTEST($sformatf("no abort of receiving when receiving 'long C2 chips' -> over current (C52142-563) of receiver %1d", receiver_selection))
				#10us;
				slave_if.cable.Current = 2;
//				load = 60.0;
				#5us;
				`FAIL_UNLESS_EQUAL(o_rec_pending, 1'b1)
				#(95us);
				`FAIL_UNLESS_EQUAL(o_rec_pending, 1'b1)
				slave_if.cable.Current = 0;
				#(time_until_response_received); // 3 chips!
				`FAIL_UNLESS_EQUAL(o_rec_pending, 1'b0)
				#10us;
			`SVTEST_END
				
			begin
				chipt_time_iterator_for_unit_tests chip_time_iterator;
				chip_time_iterator = new(common_config);
				while (chip_time_iterator.has_next()) begin
					int current_chip_time = chip_time_iterator.chip_time;
					chip_time_iterator.apply_next();
					`SVTEST($sformatf("abort pausing of regulation when receiving and over current is dependent to chip time configuration=%1dus (C52142-563) of receiver %1d", (current_chip_time), receiver_selection))
						time wait_time = (current_chip_time)*8us - 3us;
						#1us;
						slave_if.cable.Current = 2;
						#1us; // filter time
						#((current_chip_time)*1us+2us);
						`FAIL_UNLESS_EQUAL(o_rec_pending, 1'b1)
						#(wait_time);
						`FAIL_UNLESS_EQUAL(o_rec_pending, 1'b1)
						#2us;
						`FAIL_UNLESS_EQUAL(o_rec_pending, 1'b1)
						#10us;
					`SVTEST_END
				end
			end
			
			`SVTEST($sformatf("check symbol coding error with a two slave response will issue a RECFIN of receiver %1d", receiver_selection))
				bit recfin_issued = 1'b0;
				#10us;
				fork 
					begin
						send_slave_response('{4,2,2,2,0,2,4,4,2,0,4,2,4,4,4,2,2,4,2,4,2,4,4});
						#10us;
					end
					begin
						do begin
							@(posedge response_finished);
							#1;
						end
						while (response_finished != 1'b1);
						recfin_issued = 1'b1;
						#70us;
					end
				join_any
				
				#10us;
				slave_if.cable.Current = 0;
				
				`FAIL_UNLESS_EQUAL(recfin_issued, 1'b1)
			`SVTEST_END
				
			`SVTEST($sformatf("check reseting with enable=0 (C52142-582) of receiver %1d", receiver_selection))
				bit is_still_receiving;
				dsi3_slave_seq seq;
				enable = 1'b1;
				#1us;
				seq = dsi3_receiver_test_slave_sequence::create_test_seq(slave_sequencer, .symbol_count(24));
				fork
					seq.start(slave_sequencer);
					begin
						#10us;
						enable = 1'b0;
						#1us;
						if (o_rec_pending == 1'b0) begin
							fork
								begin
									do begin
										@(posedge o_rec_pending);
										#1;
									end
									while (o_rec_pending == 1'b0);
									is_still_receiving = 1'b1;
								end
								#100us; // timeout
							join_any
							disable fork;
						end
						else
							is_still_receiving = o_rec_pending;
					end
				join
				#(time_until_response_received);
				`FAIL_UNLESS_EQUAL(is_still_receiving, 1'b0)
			`SVTEST_END
			
			begin
				chipt_time_iterator_for_unit_tests chip_time_iterator;
				chip_time_iterator = new(common_config);
				while (chip_time_iterator.has_next()) begin
					chip_time_iterator.apply_next();
					for (int gap = 1; gap<6; gap++) begin
						`SVTEST($sformatf("I: check for 4 Chip gap (gap=%1dchips)(C52142-588) of receiver %1d with symbol 0xf", gap, receiver_selection))
							dsi3_slave_seq seq;
							int response[$];
							common_config.chip_time = CHIPTIME_3US;
							#1us;
							case (gap)
								1,2:	seq = dsi3_receiver_test_slave_sequence::create_test_seq_with_data(slave_sequencer, '{4'hf, 4'hf, 4'hf, 4'hf, 4'h0});		// one erroneous symbol
								3:		seq = dsi3_receiver_test_slave_sequence::create_test_seq_with_data(slave_sequencer, '{4'hf, 4'hf, 4'hf, 4'hf, 4'h0, 4'hd}); // one erroneous symbol + a 'd'-symbol
								4:		seq = dsi3_receiver_test_slave_sequence::create_test_seq_with_data(slave_sequencer, '{4'hf, 4'hf, 4'hf, 4'hf, 4'h0, 4'h0}); // two erroneous symbols
								5:		seq = dsi3_receiver_test_slave_sequence::create_test_seq_with_data(slave_sequencer, '{4'hf, 4'hf, 4'hf, 4'hf});				// second "packet" is not received
							endcase
							repeat (4) begin
								response.push_back(1);
								response.push_back(2);
								response.push_back(1);
							end
							repeat(gap)			// add c0 as gap
								response.push_back(0);
							response.push_back(2); // add a symbol 2-0-0
							repeat(4)
								response.push_back(0);
								
							send_slave_response(response);
							#20us;
							if (gap < 5) begin
								`FAIL_UNLESS_EQUAL(SYMBOL_ERROR, 1'b1)
							end
							`FAIL_UNLESS(_receive.compare_response(seq))
							`FAIL_IF(!uvm_report_mock::verify_complete());
						`SVTEST_END
					end
			
					for (int gap = 1; gap<5; gap++) begin
						`SVTEST($sformatf("II: check for 3 Chip gap (gap=%1dchips)(C52142-588) of receiver %1d with symbol 0xc", gap, receiver_selection))
							dsi3_slave_seq seq;
							int response[$];
							common_config.chip_time = CHIPTIME_3US;
							#1us;
							case (gap)
								1,2:	seq = dsi3_receiver_test_slave_sequence::create_test_seq_with_data(slave_sequencer, '{4'hc, 4'hc, 4'hc, 4'hc, 4'h0});		// one erroneous symbol
								3:		seq = dsi3_receiver_test_slave_sequence::create_test_seq_with_data(slave_sequencer, '{4'hc, 4'hc, 4'hc, 4'hc, 4'h0, 4'hd}); // one erroneous symbol + a 'd'-symbol
								4:		seq = dsi3_receiver_test_slave_sequence::create_test_seq_with_data(slave_sequencer, '{4'hc, 4'hc, 4'hc, 4'hc, 4'h0, 4'h0}); // two erroneous symbols
								5:		seq = dsi3_receiver_test_slave_sequence::create_test_seq_with_data(slave_sequencer, '{4'hc, 4'hc, 4'hc, 4'hc});				// second "packet" is not received
							endcase
							repeat (4) begin // c-symbol
								response.push_back(1);
								response.push_back(2);
								response.push_back(0);
							end
							repeat(gap)			// add c0 as gap
								response.push_back(0);
							response.push_back(2); // add a symbol 2-0-0
							repeat(4)
								response.push_back(0);
									
							send_slave_response(response);
							#20us;
							if (gap < 5) begin
								`FAIL_UNLESS_EQUAL(SYMBOL_ERROR, 1'b1)
							end
							`FAIL_UNLESS(_receive.compare_response(seq))
							`FAIL_IF(!uvm_report_mock::verify_complete());
						`SVTEST_END
					end
				end
			end
			
			`SVTEST($sformatf("III: check for 3 Chip gap (C52142-588) of receiver %1d", receiver_selection))
				dsi3_slave_seq seq;
				int response[$];
				#1us;
					// create responses
				response = '{1,2,1}; // =0xf
				repeat(2)			// add 2x C0 as gap
					response.push_back(0);
				response.push_back(2); // add a symbol 2-0-0
				repeat(6)
					response.push_back(0);
				
				// create corresponding sequences
				seq = dsi3_receiver_test_slave_sequence::create_test_seq_with_data(slave_sequencer, '{4'hf,4'h0});
						
				send_slave_response(response);
				#20us;
                void'(_receive.compare_response(seq));
				`FAIL_IF(!uvm_report_mock::verify_complete());
			`SVTEST_END
			
			for (time gap = 6us; gap<10us; gap+=50ns) begin
				`SVTEST($sformatf("check for 3 Chip gap (gap=%5.2fus)(C52142-588) of receiver %1d", gap/1.0us, receiver_selection))
					int response1[$], response2[$];
					#1us;
					response1 = '{1,2,1}; // =0xf
					response2 = '{2,2,1,2,0,1}; // =0xb7
					fork
						begin
							send_slave_response(response1);
							#gap;
							send_slave_response(response2);
						end
						begin
							
						end
					join
					#30us;
				`SVTEST_END
			end
			
			for (int symbols=257; symbols < 260; symbols++) begin
				repeat(10) begin
					`SVTEST($sformatf("Check receive timeout and symbol count error for too long PDCM packets (%1d symbols)", symbols))
						dsi3_slave_seq seq;
						common_config.chip_time = CHIPTIME_3US;
						receive_time_out = time_base + shortint'((symbols*9)-1);
						seq = dsi3_receiver_test_slave_sequence::create_test_seq(.sequencer(slave_sequencer), .symbol_count(symbols), .chiptime(3));
						seq.start(slave_sequencer);
						#10us;
						`FAIL_UNLESS_EQUAL(symbol_count_over_flow, 1'b1)
					`SVTEST_END
				end
			end
			
			for (int symbols=4; symbols < 17; symbols++) begin
				`SVTEST($sformatf("Check receiving of packets in CRM (%1d symbols) - data has to be truncated at 8 symbols", symbols))
					dsi3_slave_seq seq;
					set_mode(MODE_CRM);
					#1us;
					seq = dsi3_receiver_test_slave_sequence::create_test_seq(slave_sequencer, .symbol_count(symbols));
					fork
						seq.start(slave_sequencer);
						begin
							fork
								#200us;
								begin
									@(negedge response_finished);
									#10ns;
									enable = 1'b0;
								end
							join_any
						end
					join
					#(time_until_response_received);
                    void'(_receive.compare_response(seq));
					`FAIL_IF(!uvm_report_mock::verify_complete());
				`SVTEST_END
			end
			
            `ifdef DO_EXHAUSTIVE_RECEIVER_TESTS
			// TODO: add chiptime and tolerances!
			begin
				int logfile_fail, logfile_pass;
				dsi3_slave_seq seq;
				m52142b_slave_timing slave_timing = new();
				timing_iterator slave_timing_iterator;
				int fail_data_sets[int];
				int test_tolerance[$] = '{1000};
//				int test_tolerance[$] = '{970, 1000, 1030};
				logfile_fail = $fopen("fails.log");
				logfile_pass = $fopen("pass.log");
				stc = slave_agent.get_rxd_timing();
				slave_agent.set_rxd_timing(slave_timing);			
				slave_timing_iterator = slave_agent.get_rxd_timing_iterator();
				slave_timing_iterator.set_mode(NEXT_VALUE);

				$fdisplay(logfile_fail, "\n\n-------------------------------\nreceiver selection %1d\n-------------------------------\n\n", receiver_selection);
				$fdisplay(logfile_pass, "\n\n-------------------------------\nreceiver selection %1d\n-------------------------------\n\n", receiver_selection);
				foreach (test_data[i]) begin
					foreach (test_tolerance[j]) begin
						slave_timing_iterator.restart();
			 			write_header(logfile_fail, test_data[i], slave_timing_iterator);
						write_header(logfile_pass, test_data[i], slave_timing_iterator);
						while (slave_timing_iterator.has_next()) begin
							`SVTEST($sformatf("Check RXD timings of receiver %1d with sequence %1d | tolerance %3d%% | timing: %p", receiver_selection, i, test_tolerance[j]/10, slave_timing_iterator.current_selector()))
								bit result;
								seq = dsi3_receiver_test_slave_sequence::create_test_seq_with_data(slave_sequencer, test_data[i]);
								set_tolerance(seq, test_tolerance[j]);
								seq.start(slave_sequencer);
								#12us;
								result = _receive.compare(seq);
								current_selector = slave_timing_iterator.current_selector();
								if (!result) begin
									$fdisplay(logfile_fail, get_table_string(test_tolerance[i], slave_timing_iterator.get_table_string()));
									if (fail_data_sets.exists(current_selector.data_set)) begin
										fail_data_sets[current_selector.data_set]++;
									end
									else begin
										fail_data_sets[current_selector.data_set] = 1;
									end
								end 
			 					else begin
									$fdisplay(logfile_pass, get_table_string(test_tolerance[i], slave_timing_iterator.get_table_string()));
								end
								`FAIL_UNLESS (result == 1)
								_receive.initialize();						
							`SVTEST_END
						end
					end
				end
				begin
					int sum=0; 
			 		int modulo=32;
			 		int fail_data_sets_mod[int];
					foreach(fail_data_sets[i]) begin
						$fdisplay(logfile_fail, $sformatf("data set %3d fails: %3d", i, fail_data_sets[i]));
						sum+=fail_data_sets[i];
					end
					$fdisplay(logfile_fail, $sformatf("-----------------------------\nsum: %3d", sum));
				
					$fdisplay(logfile_fail, $sformatf("\n\n"));
				
					foreach(fail_data_sets[i]) begin
						if (fail_data_sets_mod.exists(i%modulo))
							fail_data_sets_mod[i%modulo]+=fail_data_sets[i];
						else 
							fail_data_sets_mod[i%modulo] = fail_data_sets[i];
					end
					foreach(fail_data_sets_mod[i]) begin
						$fdisplay(logfile_fail, $sformatf("data set %3d fails: %3d", i%modulo, fail_data_sets_mod[i]));
					end
				end
				slave_agent.set_rxd_timing(stc);
				$fclose(logfile_fail);
				$fclose(logfile_pass);
            end
            `endif

		// check REC_TO
		// check no receiveing if enable = 0; -> no update of smybol_count + data + rec_time_start
		enable_clk = 1'b0;
	end	 
	`SVUNIT_TESTS_END
	
	`include "p52143_413.inc.sv"
	
	task send_slave_response(int response[], time chiptime=3us);
		for(int index=0; index<response.size(); index++) begin
			slave_if.cable.Current = response[index];
			#(chiptime);
		end
		slave_if.cable.Current = 0;
	endtask
	
	function automatic void create_queue_of_symbols(l4_queue queue_of_nibbles, ref dsi3_pkg::dsi3_symbol symbols[$]);
		symbols.delete();
		while (queue_of_nibbles.size() > 0) begin
			symbols.push_back(dsi3_pkg::dsi3_symbol_lut[queue_of_nibbles[0]]);
            void'(queue_of_nibbles.pop_front());
		end
	endfunction
	
	task automatic finish_packet();
		_receive.finish(symbol_count_over_flow, symbol_count);
	endtask
		
	task automatic send_symbol(dsi3_pkg::dsi3_symbol symbol);
		timing_iterator slave_timing_iterator;
		slave_rxd_timing rxd_timing;
		dsi3_slave_test_driver driver; 
		#0;	
		if (!$cast(driver, _top_config._dsi3_slave_agent.m_driver)) $fatal("Wrong driver version initiated");
		slave_timing_iterator = slave_agent.get_rxd_timing_iterator();
		rxd_timing = slave_timing_iterator.next();
		driver.send_test_symbol(symbol, rxd_timing);
	endtask
	
	function automatic string get_header(l4_queue data, string timing);
		string s="Data =";
		for (int i=0; i<data.size(); i++) begin
			s={s, $sformatf("%1h",data[i])};
			if ((i[1:0]==0) && (i>0)) begin
				s={s, " "};
			end
		end
		s = {s, "\n", $sformatf("tolerance | %s", timing)};
		return s;
	endfunction
		
	function automatic string get_table_string(int tolerance, string timing);
		return $sformatf("  %6.1f%% | %s", (tolerance-1000.0)/10.0, timing);
	endfunction
	
	function automatic void write_header(int file, l4_queue data, timing_iterator slave_timing_iterator);
		$fdisplay(file, "---------------------------------------------------------------------------------------------------------------------");
		$fdisplay(file, get_header(data, slave_timing_iterator.get_table_header()));
	endfunction
endmodule
