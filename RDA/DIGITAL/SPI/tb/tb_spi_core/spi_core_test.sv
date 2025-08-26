`include "svunit_defines.svh"
`include "clk_rst_define.sv"

module spi_core_test import project_pkg::*; ();
	
	`include "uvm_macros.svh"
	
	typedef enum {AUTOMATIC, MANUAL} data_generation_e;
	
	data_generation_e	tx_transmit;
	
	import svunit_uvm_mock_pkg::*;
	import svunit_pkg::svunit_testcase;
	import common_pkg::crc_ccitt_16;
	import addresses_pkg::*;
	import common_test_pkg::*;
	import uvm_pkg::*;
	import spi_unit_test_pkg::*;
	import spi_pkg::*;
	import spi_implementation_pkg::*;
	
	string name = "spi_core_test";
	svunit_testcase svunit_ut;
	
	spi_sequencer	sequencer;
	
	top_config		_top_config;
	spi_if			spi_if_agent();
	spi_int_if		spi_if_dut();
	
	check_service		_check;
	
	wire	sck;
	pulldown(sck);
	assign	sck = spi_if_agent.SCK;
	
	ecc_error_if #(.WIDTH (1)) ecc_error ();
	
	// interface mapping between SPI agent and DUT
	assign	spi_if_dut.csb = spi_if_agent.CSN;
	assign	spi_if_dut.csb_resn = ~spi_if_agent.CSN;
	assign	spi_if_dut.sck = sck;
	assign	spi_if_dut.sdi = spi_if_agent.SDI;
	assign	spi_if_agent.SDO = spi_if_dut.sdo;
	
	`clk_def(27777ps)
	
	initial begin
		_top_config = new("_top_config");
		uvm_config_db #(top_config)::set(null, "uvm_test_top", "_top_config", _top_config);
		uvm_config_db #(top_config)::set(null, "uvm_test_top.m_env", "_top_config", _top_config);
		_top_config._spi_config.vif	= spi_if_agent;
		
		run_test();
	end
	
	//===================================
	// This is the UUT that we're
	// running the Unit Tests on
	//===================================
	logic rxd_valid, txd_en_clear, tx_data_available_synced, command_running;
	logic	disable_core_command_interpretation;
	data_t	status_word;
	data_ecc_t rx_data, tx_data;
	data_t	current_crc_in, current_crc_out;
	logic	transfer_incomplete, word_based_crc_of_input_correct;
	
	spi_core i_spi_core (
		.spi_i               (spi_if_dut.slave ),
		.clk_rst             (clk_rst.slave    ),
		.i_tx_data_available_synced (tx_data_available_synced),
		.i_tx_data           (tx_data          ),
		.i_status_word       (status_word      ),
		.i_command_running   (command_running  ),
		.i_disable_core_command_interpretation  (disable_core_command_interpretation ),
		.o_txd_en_clear      (txd_en_clear     ),
		.o_data_received     (rx_data          ),
		.o_rxd_valid         (rxd_valid        ),
		.o_transfer_incomplete(transfer_incomplete),
		.o_word_based_crc_of_input_correct(word_based_crc_of_input_correct),
		.ecc_error           (ecc_error.master ));
	
	logic [1:0] transfer_incomplete_fifo = 1'b0;
	
	assign current_crc_in = i_spi_core.crc_in;
	assign current_crc_out = i_spi_core.crc_out;
	
	initial begin
		command_running = 1'b0;
		disable_core_command_interpretation = 1'b0;
	end
	
	always@(edge rxd_valid) begin
		automatic bit incomplete = transfer_incomplete_fifo[0] ^ transfer_incomplete;
		if (_check == null)
			_check = _top_config._check_service;
		_check.set_received_word(rx_data);
		_check.set_crc_in(current_crc_in);
		_check.set_crc_out(current_crc_out);
		_check.set_command_pending_flag(command_running);
		_check.add_incomplete_flag(incomplete);
		
		_check.set_status_word(status_word);
		status_word = 16'($urandom_range(16'hffff, 0));
		begin
			case (tx_transmit)
				MANUAL: begin
				end
				AUTOMATIC: begin
					tx_data.data = 16'($urandom_range(16'hffff, 0));
					tx_data.ecc = 6'(DWF_ecc_gen_chkbits(16,6,tx_data.data));
					tx_data_available_synced = 1'($urandom_range(1, 0));
				end
			endcase
			_check.set_transmitted_word(tx_data, tx_data_available_synced);
		end
		transfer_incomplete_fifo = {transfer_incomplete_fifo[0], transfer_incomplete};
	end
	
	always@(negedge spi_if_dut.csb) begin
		
	end
	
	always@(edge txd_en_clear) begin
		tx_data_available_synced = 1'b0;
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
		/* Place Setup Code Here */
		uvm_report_mock::setup();
		_check = _top_config._check_service;
		_check.initialize();
		command_running = 1'b0;
		tx_data_available_synced = 1'b0;
		status_word = 16'haffe;
		tx_data.data = '0;
		tx_data.ecc = project_pkg::ECC_FOR_DATA_0;
		tx_transmit = MANUAL;
		disable_core_command_interpretation = 1'b0;
		#1us;
	endtask
	
	//===================================
	// Here we deconstruct anything we
	// need after running the Unit Tests
	//===================================
	task teardown();
		svunit_ut.teardown();
		/* Place Teardown Code Here */
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
	
	task reset_all();
		set_por();
		_check.initialize();
		spi_if_agent.CSN = 1'b1;
	endtask
	
	function automatic int get_errors();
		int errors;
		errors += _check.get_error_count();
		_check.finish_test();
		errors += (!uvm_report_mock::verify_complete()) ? 1 : 0;
		return errors;
	endfunction
	
	`SVUNIT_TESTS_BEGIN
	enable_clk = 1'b1;
	#10us;
	sequencer = _top_config._spi_agent.m_sequencer;
	
	/*FIXME: add test:
	 * - reset CRC with CRC command and reset command
	 * - CSB no influence on frame
	 * - status word output after CRC command
	 *   - add test for CSB before output of status word 
	 * - reset command resets CRC to seed
	 * - errors when CSB is not alligned to 16 Bit
	 * - disable_core_command_interpretation
	 * - crc_in_correct
	 * - word_based_crc_of_input_correct
 	 */
	
	//#######################################################################
	for (int i=0; i<10; i++) begin
		automatic spi_seq	seq;
		int words = $urandom_range(10, 1);
		`SVTEST ($sformatf("%2d: Check for in and out data with %2d words", i, words))
		tx_transmit = AUTOMATIC;
		seq = spi_test_seq::create_test_seq(sequencer, words);
		seq.start(sequencer);
		#1us;
		`FAIL_UNLESS_EQUAL(get_errors(), 0)
		`SVTEST_END
	end
	
	reset_all();
	
	//#######################################################################
	for (int i=0; i<100; i++) begin
		spi_seq	seq;
		int words = $urandom_range(100, 3);
		`SVTEST ($sformatf("%2d: Check output of CRC with %2d words", i, words))
		seq = spi_test_seq::create_test_seq(sequencer, words);
		insert_crc_commands(seq);
		seq.start(sequencer);
		#10us;
		`FAIL_UNLESS_EQUAL(get_errors(), 0)
		`SVTEST_END
	end
	
	//#######################################################################
	for (int i=0; i<100; i++) begin
//		spi_seq	seq;
		int words = $urandom_range(100, 3);
		`SVTEST ($sformatf("%2d: Check output of status word with %2d words", i, words))
//		seq = spi_test_seq::create_test_seq(sequencer, words);
//		insert_status_word_commands(seq);
//		seq.start(sequencer);
//		#10us;
		`FAIL_UNLESS_EQUAL(1 /*get_errors()*/, 0)
		`SVTEST_END
	end
	
	//#######################################################################
	`SVTEST ($sformatf("Check no status word output when command pending"))
//	spi_seq	seq;
//	seq = spi_test_seq::create_test_seq(sequencer, 200);
//	// set CRC output
//	for (int i=0; i<seq.data_in.size(); i+=2) begin
//		seq.data_in[i][15:12]=project_pkg::IC_STATUS;
//	end
//	fork
//		seq.start(sequencer);
//		forever begin
//			@(edge rxd_valid);
//			if (rx_data[15:12] == project_pkg::IC_STATUS)
//				command_running = 1'($urandom_range(1, 0));
//		end
//	join_any
//	disable fork;
//	
//	`FAIL_UNLESS_EQUAL(get_errors(), 0)
	`FAIL_UNLESS_EQUAL(1, 0)
	`SVTEST_END
	
	//#######################################################################
	`SVTEST ($sformatf("Check no CRC output when command pending"))
	spi_seq	seq;
	seq = spi_test_seq::create_test_seq(sequencer, 200);
	// set CRC output
	for (int i=0; i<200; i+=2) begin
		seq.data_in[i][15:12]=CRC_OUT;
	end
	
	fork
		seq.start(sequencer);
		forever begin
			@(edge rxd_valid);
			if (rx_data[15:12] == CRC_OUT)
				command_running = 1'($urandom_range(1, 0));
		end
	join_any
	disable fork;
	
	`FAIL_UNLESS_EQUAL(get_errors(), 0)
	`SVTEST_END
	
	//#######################################################################
	`SVTEST ($sformatf("Check sending of data"))
	spi_seq	seq;
	seq = spi_test_seq::create_test_seq(sequencer, 200);
	tx_transmit = AUTOMATIC;
	
	seq.start(sequencer);
	
	`FAIL_UNLESS_EQUAL(get_errors(), 0)
	`SVTEST_END
	
	//#######################################################################
	for (int bit_count = 1; bit_count <17; bit_count++) begin
		`SVTEST ($sformatf("Check incomplete Flag with %1d bits in last word", bit_count))
		spi_command_frame_seq frame = new();
		frame.crc_in_enable = 1;
		frame.crc_in_correct = 1;
		begin
			spi_write_master_register_seq seq = new();
			seq.randomize() with {address == ADDR_INTERRUPT_IRQ_MASK[11:0]; data == 16'h0000;};
			frame.add_command(seq);
		end
		frame.crc_bit_count = bit_count;
		frame.start(sequencer);
		#1us;
		if (bit_count != 16) begin
			`FAIL_UNLESS_EQUAL(~transfer_incomplete_fifo[0], transfer_incomplete_fifo[1])
		end
		else begin
			`FAIL_UNLESS_EQUAL(transfer_incomplete_fifo[0], transfer_incomplete_fifo[1])
		end
		`SVTEST_END
	end
	
	enable_clk = 1'b0;
	`SVUNIT_TESTS_END
	
	function void insert_crc_commands(spi_seq t);
		for (int i=0; i< t.data_in.size(); i+=$urandom_range(3,1)) begin
			t.data_in[i][15:12]=CRC_OUT;
		end
	endfunction
	
//	function void insert_status_word_commands(spi_seq t);
//		for (int i=0; i< t.data_in.size(); i+=$urandom_range(4,1)) begin
//			t.data_in[i][15:12]=project_pkg::IC_STATUS;
//		end
//	endfunction
	
endmodule
