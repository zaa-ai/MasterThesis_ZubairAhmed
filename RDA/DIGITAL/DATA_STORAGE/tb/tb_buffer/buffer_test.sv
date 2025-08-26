`include "svunit_defines.svh"
`include "clk_rst_define.sv"

module buffer_test import project_pkg::*; ();
	
	`include "uvm_macros.svh"
	
	import svunit_pkg::svunit_testcase;
	import svunit_uvm_mock_pkg::*;
	import crc_calculation_pkg::spi_crc_ccitt_16;
	import addresses_pkg::*;
	import common_test_pkg::*;
	import uvm_pkg::*;
	import buffer_reader_pkg::*;
	import buffer_writer_pkg::*;
	import unit_test_pkg::*;
	import elip_bus_pkg::*;

	string name = "buffer_test";
	svunit_testcase svunit_ut;
	
	buffer_writer_agent			writer_agent;
	buffer_writer_sequencer_t	writer_sequencer;
	
	buffer_reader_agent 		reader_agent;
	buffer_reader_sequencer_t	reader_sequencer;
	
	elip_bus_sequencer_t		elip_sequencer;
	
	top_config		_top_config;
	
	check_service		_check;
	
	`clk_def(27777ps)
	
	buffer_reader_if reader_if ();
	buffer_writer_if writer_if ();
	
	elip_if #(.addr_width(16), .data_width(16)) elip_registers();
	elip_full_if elip();
	
	elip_bus_if elip_bus_registers();
	elip_bus_if elip_bus_buffer();
	
	ecc_error_if #(.WIDTH (1)) ecc_error ();
	
	data_t	elip_register_read;
	logic	data_available;
	
	initial begin
		_top_config = new("_top_config");
		uvm_config_db #(top_config)::set(null, "uvm_test_top", "_top_config", _top_config);
		uvm_config_db #(top_config)::set(null, "uvm_test_top.m_env", "_top_config", _top_config);
		
		_top_config._writer_config.vif = writer_if;
		_top_config._writer_config.vif_clk_rst = clk_rst;
		_top_config._reader_config.vif = reader_if;
		_top_config._reader_config.vif_clk_rst = clk_rst;
		
		_top_config._elip_register_config.vif	= elip_bus_registers;
		_top_config._elip_buffer_config.vif		= elip_bus_buffer;
		
		run_test();
	end
	
	//===================================
	// This is the UUT that we're 
	// running the Unit Tests on
	//===================================
	
	localparam	buffer_size = 'h20;
	localparam	buffer_offset = 'h200;
	
	buffer #(
		.ADDR_WIDTH      (16),
		.BASE_ADDR       (BASE_ADDR_DSI_CMD_STAT[0]),
		.BUFFER_OFFSET_ADDRESS  ('h200), 
		.BUFFER_SIZE     (buffer_size), 
		.PRIORITY_READ   (0    )
	) i_buffer (
		.clk_rst         (clk_rst.slave        ), 
		.reader          (reader_if.slave      ), 
		.writer          (writer_if.slave      ), 
		.elip            (elip.master          ),
		.elip_registers  (elip_registers.slave ),
		.o_data_available(data_available ),
		.o_elip_registers_data_out(elip_register_read),
		.ecc_error       (ecc_error.master      )
	);
	
	interface_converter_elip_full_2_elip_bus i_interface_converter_data_buffer (
			.clk_rst    (clk_rst.slave             ),
			.elip_full  (elip.slave    ), 
			.elip_bus   (elip_bus_buffer  ));
	
	interface_converter_elip_bus_2_elip #(.data_width  (16 )) i_interface_converter_registers (
			.clk_rst     (clk_rst.slave    ), 
			.elip_bus    (elip_bus_registers   ), 
			.elip        (elip_registers.master       ), 
			.i_data_out  (elip_register_read   ));
	
	ram_model ram_model (
			.clk_rst   (clk_rst.slave  ), 
			.elip      (elip.slave     ) 
		);
	
	//===================================
	// Build
	//===================================
	function void build();
		svunit_ut = new(name);
	endfunction
	
	typedef struct packed unsigned {
		logic[3:0]	unused;
		logic[11:0]	valid_count;
	} buf_stat_t;
	
	buffer_write_seq	wr_seq;
	buffer_read_seq		rd_seq;
	data_t		read_data;
	buf_stat_t	read_stat;
	

	//===================================
	// Setup for running the Unit Tests
	//===================================
	task setup();
		svunit_ut.setup();
		/* Place Setup Code Here */
		uvm_report_mock::setup();
		_wait(1);
		set_por();
		_check = _top_config._check_service;
		_check.initialize();
		_check.set_buffer_offset(buffer_offset);
		_check.set_buffer_size(buffer_size);
		_wait(5);
		wr_seq = new();
		rd_seq = new();
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
	
	function automatic int get_errors();
		int errors = 0;
		if (!uvm_report_mock::verify_complete())
			errors++;
		errors += _check.get_error_count();
		return errors;
	endfunction
	
	/*###   reading tasks   ######################################################*/
	function automatic buffer_read_seq get_read_seq(int number_of_words);
		buffer_read_seq tr = new();
		tr.randomize with {data.size() == number_of_words;};
		return tr;
	endfunction
	
	task automatic read(buffer_read_seq t);
		t.start(reader_sequencer);
	endtask
	
	task automatic read_words(input int number_of_words);
		rd_seq = get_read_seq(number_of_words);
		read(rd_seq);
	endtask
	
	task automatic step(int	steps);
		buffer_step_seq step_seq = new("step_seq");
		step_seq.step = steps;
		step_seq.start(reader_sequencer);
	endtask
	
	/*###   writing tasks   ######################################################*/
	function automatic buffer_write_seq get_write_seq(int number_of_words, bit valid=1'b1, bit do_validation=1'b1);
		buffer_write_seq tr = new();
		tr.randomize with {data.size() == number_of_words; do_validation == local::do_validation; valid == local::valid;};
		return tr;
	endfunction
	
	task automatic write(buffer_write_seq t);
		t.start(writer_sequencer);
	endtask
	
	task automatic write_words(input int number_of_words);
		wr_seq = get_write_seq(number_of_words);
		write(wr_seq);
	endtask
	
	/*###   other tasks   ######################################################*/
	task _wait(input int wait_cycles=2);
		wait_for_n_clocks(wait_cycles);
	endtask
	
	task automatic read_elip (input elip_addr_t address, output data_t data);
		elip_read_seq	seq = new();
		seq.address = address;
		seq.start(elip_sequencer);
		data = seq.req.data_read[15:0];
	endtask
	
	task automatic write_elip(input elip_addr_t address, input data_t data);
		elip_write_seq	seq = new();
		seq.address = address;
		seq.data = data;
		seq.ecc  = buffer_reader_pkg::DWF_ecc_gen_chkbits(16, 6, data);
		seq.start(elip_sequencer);
	endtask
	
	task automatic read_status();
		read_elip(ADDR_DSI_CMD_STAT_0_BUF_VALID_COUNT, read_data);
		read_stat = read_data;
	endtask
	
	/*###   TEST CASES   ######################################################*/
	`SVUNIT_TESTS_BEGIN
		enable_clk = 1'b1;
		#10us;
		writer_sequencer = _top_config._writer_agent.m_sequencer;
		reader_sequencer = _top_config._reader_agent.m_sequencer;
		elip_sequencer	 = _top_config._elip_register_agent.m_sequencer;

		`SVTEST ($sformatf("check flags after reset"))
			`FAIL_UNLESS_EQUAL(reader_if.empty , 1'b1)
			`FAIL_UNLESS_EQUAL(writer_if.full  , 1'b0)
			`FAIL_UNLESS_EQUAL(writer_if.nearly_full , 1'b0)
			`FAIL_IF(!uvm_report_mock::verify_complete());
		`SVTEST_END
		
		`SVTEST ($sformatf("check status flags in registers  after reset"))
			read_status();
			`FAIL_UNLESS_EQUAL(read_stat, 0)
		`SVTEST_END
		
		`SVTEST ($sformatf("read when empty --> '0"))
			rd_seq = get_read_seq(1);
			read(rd_seq);
			_wait();
			`FAIL_UNLESS_EQUAL(rd_seq.data[0], 0)
			`FAIL_UNLESS_EQUAL(get_errors(), 0)
			`FAIL_IF(!uvm_report_mock::verify_complete());
		`SVTEST_END
			
		`SVTEST ($sformatf("read not validated data --> still '0"))
			write(get_write_seq(.number_of_words(5),.do_validation(1'b0)));
			_wait();
			rd_seq = get_read_seq(1);
			read(rd_seq);
			_wait();
			
			`FAIL_UNLESS_EQUAL(rd_seq.data[0], 0)
			`FAIL_UNLESS_EQUAL(get_errors(), 0)
			`FAIL_IF(!uvm_report_mock::verify_complete());
		`SVTEST_END
		
		`SVTEST ($sformatf("write and read one word"))
			write_words(1);
			_wait();
			read_words(1);
			_wait();
			`FAIL_UNLESS_EQUAL(wr_seq.data[0], rd_seq.data[0])
			`FAIL_UNLESS_EQUAL(get_errors(), 0)
			`FAIL_IF(!uvm_report_mock::verify_complete());
		`SVTEST_END
		
		`SVTEST ($sformatf("check buffer fill warning - border check"))
			write_words((buffer_size/4*3)-1);
			_wait();
			`FAIL_UNLESS_EQUAL(writer_if.nearly_full, 1'b0)
			`FAIL_UNLESS_EQUAL(writer_if.full  , 1'b0)
			write_words(1);
			_wait();
			`FAIL_UNLESS_EQUAL(writer_if.nearly_full, 1'b1)
			`FAIL_UNLESS_EQUAL(writer_if.full  , 1'b0)
			read_words(1);
			_wait();
			`FAIL_UNLESS_EQUAL(writer_if.nearly_full, 1'b0)
			`FAIL_UNLESS_EQUAL(writer_if.full  , 1'b0)
			`FAIL_IF(!uvm_report_mock::verify_complete());
		`SVTEST_END	
		
		`SVTEST ($sformatf("check buffer full error - border check"))
			write_words(buffer_size - 2);
			_wait();
			`FAIL_UNLESS_EQUAL(writer_if.full, 1'b0)
			`FAIL_UNLESS_EQUAL(writer_if.nearly_full, 1'b1)
			write_words(1);
			_wait();
			`FAIL_UNLESS_EQUAL(writer_if.full, 1'b1)
			`FAIL_UNLESS_EQUAL(writer_if.nearly_full, 1'b1)
			write_words(1);
			_wait();
			`FAIL_UNLESS_EQUAL(writer_if.full, 1'b1)
			`FAIL_UNLESS_EQUAL(writer_if.nearly_full, 1'b1)
			read_words(1);
			_wait();
			`FAIL_UNLESS_EQUAL(writer_if.full, 1'b0)
			`FAIL_UNLESS_EQUAL(writer_if.nearly_full, 1'b1)
			`FAIL_IF(!uvm_report_mock::verify_complete());
		`SVTEST_END	
		
		`SVTEST ($sformatf("check full buffer does not overwrite data"))
			write_words(buffer_size-1);
			`FAIL_UNLESS_EQUAL(writer_if.full, 1'b1)
			write_words(2);
			_wait();
			`FAIL_UNLESS_EQUAL(writer_if.full, 1'b1)
			read_words(buffer_size);
			_wait();
			`FAIL_UNLESS_EQUAL(reader_if.empty , 1'b1)
			`FAIL_IF(!uvm_report_mock::verify_complete());
		`SVTEST_END		
			
		`SVTEST ($sformatf("check write pointer"))
			data_t	write_pointer;
			wr_seq = get_write_seq(1, 1'b1, 1'b0);
			read_elip(ADDR_DSI_CMD_STAT_0_BUF_WRITE_POINTER, write_pointer);
			`FAIL_UNLESS_EQUAL(write_pointer, data_t'(buffer_offset))
			
			$write("check write pointer write");
			for (int i=0; i<buffer_size+5; i++) begin 
				$write(" %1d",i);
				write(wr_seq);
				_wait();
				read_elip(ADDR_DSI_CMD_STAT_0_BUF_WRITE_POINTER, write_pointer);
				if (i<buffer_size-2) begin
					`FAIL_UNLESS_EQUAL(write_pointer, data_t'(buffer_offset+i+1))
				end
				else begin
					`FAIL_UNLESS_EQUAL(write_pointer, data_t'(buffer_offset+buffer_size-1))
				end
			end
			$write("\n");
			`FAIL_UNLESS_EQUAL(get_errors(), 0)
			`FAIL_IF(!uvm_report_mock::verify_complete());
		`SVTEST_END
			
		`SVTEST ($sformatf("check valid pointer"))
			data_t	valid_pointer;
			read_elip(ADDR_DSI_CMD_STAT_0_BUF_VALID_POINTER, valid_pointer);
			`FAIL_UNLESS_EQUAL(valid_pointer, data_t'(buffer_offset))
			$write("check valid pointer write");
			for (int i=0; i<buffer_size+5; i++) begin 
				$write(" %1d",i);
				write_words(1);
				_wait();
				read_elip(ADDR_DSI_CMD_STAT_0_BUF_VALID_POINTER, valid_pointer);
				if (i<buffer_size-1) begin
					`FAIL_UNLESS_EQUAL(valid_pointer, data_t'(buffer_offset+i+1))
				end
				else begin
					`FAIL_UNLESS_EQUAL(valid_pointer, data_t'(buffer_offset+buffer_size-1))
				end
			end
			$write("\n");
			`FAIL_UNLESS_EQUAL(get_errors(), 0)
			`FAIL_IF(!uvm_report_mock::verify_complete());
		`SVTEST_END
		
		`SVTEST ($sformatf("check read pointer"))
			data_t	read_pointer;
			read_elip(ADDR_DSI_CMD_STAT_0_BUF_READ_POINTER, read_pointer);
			`FAIL_UNLESS_EQUAL(read_pointer, data_t'(buffer_offset))
			write_words(buffer_size-1);

			$write("check read pointer write");
			for (int i=0; i<buffer_size+5; i++) begin 
				$write(" %1d",i);
				read_words(1);
				_wait();
				read_elip(ADDR_DSI_CMD_STAT_0_BUF_READ_POINTER, read_pointer);
				if (i<buffer_size-1) begin
					`FAIL_UNLESS_EQUAL(read_pointer, data_t'(buffer_offset+i+1))
				end
				else begin
					`FAIL_UNLESS_EQUAL(read_pointer, data_t'(buffer_offset+buffer_size-1))
				end
			end
			$write("\n");
			`FAIL_UNLESS_EQUAL(get_errors(), 0)
			`FAIL_IF(!uvm_report_mock::verify_complete());
		`SVTEST_END
			
		`SVTEST ($sformatf("check number of free cells"))
			data_t	free_cells;
			read_elip(ADDR_DSI_CMD_STAT_0_BUF_FREE, free_cells);
			`FAIL_UNLESS_EQUAL(free_cells, data_t'(buffer_size-1))
			$write("check free cells write");
			for (int i=0; i<buffer_size+5; i++) begin 
				$write(" %1d",i);
				write_words(1);
				_wait();
				read_elip(ADDR_DSI_CMD_STAT_0_BUF_FREE, free_cells);
				if (i<buffer_size-2) begin
					`FAIL_UNLESS_EQUAL(free_cells, data_t'(buffer_size-i-2))
				end
				else begin
					`FAIL_UNLESS_EQUAL(free_cells, 0)
				end
			end
			$write("\n");
			`FAIL_UNLESS_EQUAL(get_errors(), 0)
			`FAIL_IF(!uvm_report_mock::verify_complete());
		`SVTEST_END	
			
		`SVTEST ($sformatf("check number of free cells without validation"))
			data_t	free_cells;
			read_elip(ADDR_DSI_CMD_STAT_0_BUF_FREE, free_cells);
			wr_seq = get_write_seq(1, 1'b1, 1'b0);
			`FAIL_UNLESS_EQUAL(free_cells, data_t'(buffer_size-1))
			$write("check free cells write");
			for (int i=0; i<buffer_size+5; i++) begin 
				$write(" %1d",i);
				write(wr_seq);
				_wait();
				read_elip(ADDR_DSI_CMD_STAT_0_BUF_FREE, free_cells);
				if (i<buffer_size-2) begin
					`FAIL_UNLESS_EQUAL(free_cells, data_t'(buffer_size-i-2))
				end
				else begin
					`FAIL_UNLESS_EQUAL(free_cells, 0)
				end
			end
			$write("\n");
			`FAIL_UNLESS_EQUAL(get_errors(), 0)
			`FAIL_IF(!uvm_report_mock::verify_complete());
		`SVTEST_END	
			
		`SVTEST ($sformatf("check valid count"))
			data_t	status;
			read_status();
			`FAIL_UNLESS_EQUAL(read_stat.valid_count, 0)
			$write("check valid count write");
			for (int i=0; i<buffer_size+5; i++) begin 
				$write(" %1d",i);
				write_words(1);
				_wait();
				read_status();
				if (i<buffer_size-1) begin
					`FAIL_UNLESS_EQUAL(read_stat.valid_count, 12'(i+1))
				end
				else begin
					`FAIL_UNLESS_EQUAL(read_stat.valid_count, 12'(buffer_size-1))
				end
			end
			$write("\n");
			`FAIL_UNLESS_EQUAL(get_errors(), 0)
			`FAIL_IF(!uvm_report_mock::verify_complete());
		`SVTEST_END
			
		`SVTEST ($sformatf("check valid count without validation"))
			data_t	status;
			read_status();
			`FAIL_UNLESS_EQUAL(read_stat.valid_count, 0)
			wr_seq = get_write_seq(1, 1'b1, 1'b0);
			$write("check valid count write");
			for (int i=0; i<buffer_size+5; i++) begin 
				$write(" %1d",i);
				write(wr_seq);
				_wait();
				read_status();
				`FAIL_UNLESS_EQUAL(read_stat.valid_count, 0)
			end
			$write("\n");
			`FAIL_UNLESS_EQUAL(get_errors(), 0)
			`FAIL_IF(!uvm_report_mock::verify_complete());
		`SVTEST_END
			
		`SVTEST ($sformatf("check move_pointer"))
			write_words(buffer_size-1);
			for (int i=0; i<3; i++) begin
				data_t	read_pointer, read_pointer_new;
				$display("loop=%1d", i);
				read_elip(ADDR_DSI_CMD_STAT_0_BUF_READ_POINTER, read_pointer);
				step(3);
				_wait();
				read_elip(ADDR_DSI_CMD_STAT_0_BUF_READ_POINTER, read_pointer_new);
				`FAIL_UNLESS_EQUAL(read_pointer+data_t'(3), read_pointer_new);
			end
		`SVTEST_END
		
		`SVTEST ($sformatf("check move_pointer at buffer border"))
			data_t	read_pointer;
			write_words(buffer_size-1);
			read_words(buffer_size-5);
			write_words(10);
			step(10);
			_wait();
			read_elip(ADDR_DSI_CMD_STAT_0_BUF_READ_POINTER, read_pointer);
			`FAIL_UNLESS_EQUAL(read_pointer, data_t'(5+buffer_offset))
		`SVTEST_END
			
			
//FIXME: check read and write at the same time --> prio!
// How to change prio --> other test???
//		`SVTEST ($sformatf("check read and write at the same time --> prio!"))
//			
//			`FAIL_IF(1)
//			`FAIL_IF(!uvm_report_mock::verify_complete());
//		`SVTEST_END
					
//		`SVTEST ($sformatf("check write_first"))
//			`FAIL_IF(1);
//		`SVTEST_END
//		
//			
//		`SVTEST ($sformatf("check invalid accesses"))
//			`FAIL_IF(1);
//		`SVTEST_END
		
		//FIXME: check random accesses
//		`define LOOPS 10
//		`SVTEST ($sformatf("check random access"))
//			fork
//				begin
//					repeat(`LOOPS) begin
//						rd_seq.req = get_transaction($urandom_range(8,1));
//						rd_seq.start(reader_sequencer);
//						$display({"reader: ", rd_seq.req.convert2string()});
//						#($urandom_range(5,0)*1us);
//					end
//				end
//				begin
//					repeat(`LOOPS) begin
//						wr_seq.req = get_transaction($urandom_range(8,1));
//						wr_seq.start(writer_sequencer);
//						$display({"writer: ", wr_seq.req.convert2string()});
//						#($urandom_range(5,0)*1us);
//					end
//				end
//			join
//			`FAIL_UNLESS_EQUAL(get_errors(), 0)
//			`FAIL_IF(!uvm_report_mock::verify_complete());
//		`SVTEST_END
		
		enable_clk = 1'b0;
	`SVUNIT_TESTS_END
		
endmodule
