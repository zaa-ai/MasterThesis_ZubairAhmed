`include "svunit_defines.svh"
`include "clk_rst_define.sv"
`include "DW_ecc_function.inc"

//`define SRAM_INST i_ram_wrapper_ecc.i_SRAM_3072X23U18
`define SRAM_INST i_ram_wrapper_ecc_with_bist.utils_sram_with_bist_inst.utils_sram_scan_shell_inst.sync_sram_inst.sram_inst
`define ECC_RAM_ADDR i_ram_wrapper_ecc_with_bist.utils_sram_with_bist_inst.generate_ram_with_ecc.utils_sram_ecc_inst[0].addr

module sram_ecc_test import project_pkg::*; ();

	`include "uvm_macros.svh"

	import svunit_pkg::svunit_testcase;
	import svunit_uvm_mock_pkg::*;
	import crc_calculation_pkg::spi_crc_ccitt_16;
	import addresses_pkg::*;
	import common_test_pkg::*;
	import uvm_pkg::*;
	import unit_test_pkg::*;
	import elip_bus_pkg::*;
	import ECC_pkg::*;

	localparam  LENGTH_OF_SRAM = SRAM_DEPTH;

	string name = "sram_ecc_test";
	svunit_testcase svunit_ut;

	elip_bus_sequencer_t	jtag_sequencer;
	elip_bus_sequencer_t	elip_sequencer;

	top_config				_top_config;

	`clk_def(27777ps)

	elip_if #(.addr_width(16), .data_width(16)) elip_registers();
	elip_full_if elip_ram();
	jtag_bus_if #(8, 16) jtag_bus ();

	elip_bus_if elip_bus_jtag();
	elip_bus_if elip_bus_ram();

	jtag_dr_for_registers_t	jtag_dr_read;

	logic ecc_fail, ecc_corr;
	logic ecc_fail_reg, ecc_corr_reg;
	logic [15:0] sram_cell_data;
	logic [15:0] sram_cell_addr;
	error_t sram_data_err;
	error_t sram_addr_err;
	logic forcing_data, release_data;
	event reset_ecc_flags;

	initial begin
		_top_config = new("_top_config");
		uvm_config_db #(top_config)::set(null, "uvm_test_top", "_top_config", _top_config);
		uvm_config_db #(top_config)::set(null, "uvm_test_top.m_env", "_top_config", _top_config);

		_top_config._elip_jtag_config.vif	= elip_bus_jtag;
		_top_config._elip_ram_config.vif	= elip_bus_ram;
		forcing_data = 1'b0;
		release_data = 1'b0;
		sram_data_err = NO_BIT_ERR;
		sram_addr_err = NO_BIT_ERR;
		sram_cell_data = '0;
		run_test();

	end

	//===================================
	// This is the UUT that we're
	// running the Unit Tests on
	//===================================
	ecc_error_if ecc_error ();
	ram_wrapper_ecc_with_bist i_ram_wrapper_ecc_with_bist (
			.clk_rst      (clk_rst         ),
			.elip         (elip_ram        ),
			.jtag_bus     (jtag_bus        ),
			.i_scan_mode  (1'b0            ),
			.o_jtag_dr    (jtag_dr_read    ),
			.ecc_error    (ecc_error.master));
	
	logic[SRAM_ADDR_WIDTH+DATA_WIDTH-1:0] i_wdata;
	logic[6:0]	ecc_sram;
	ecc_7_hd4_calc #(
		.DATA_WIDTH  (SRAM_ADDR_WIDTH+DATA_WIDTH ), 
		.SERIAL      (0     )
		) i_ecc_7_hd4_calc (
		.i_data      (i_wdata   ), 
		.i_ecc       (7'd0      ), 
		.o_ecc       (ecc_sram  ));
	
	task automatic get_sram_data(data_t	data, logic[SRAM_ADDR_WIDTH-1:0] address , output logic[SRAM_WIDTH-1:0] sram_data);
		i_wdata = {address, data};
		#1;
		sram_data = {ecc_sram, data};
	endtask

	// ECC fail/corrected fetch flip flop
	always@(posedge clk_rst.clk or negedge clk_rst.rstn)	begin
		if (clk_rst.rstn == 1'b0) begin
			ecc_fail_reg <= 1'b0;
			ecc_corr_reg <= 1'b0;
		end
		else begin
			ecc_fail_reg <= (ecc_fail_reg | ecc_error.double_error);
			ecc_corr_reg <= (ecc_corr_reg | ecc_error.single_error);
		end
	end
	
	always@(reset_ecc_flags) begin
		ecc_fail_reg <= 1'b0;
		ecc_corr_reg <= 1'b0;
	end

	assign	elip_ram.addr = elip_bus_ram.address;
	assign	elip_ram.rd = elip_bus_ram.read;
	assign	elip_ram.wr = elip_bus_ram.write;
	assign	elip_ram.data_write.data = elip_bus_ram.data_write;
	assign  elip_ram.data_write.ecc  = elip_bus_ram.data_write_ecc;
	assign	elip_bus_ram.data_read = elip_ram.data_read.data;
	assign  elip_bus_ram.data_read_ecc = elip_ram.data_read.ecc;
	assign	elip_bus_ram.ready = elip_ram.ready;
	assign	elip_bus_ram.clk = clk_rst.clk;
	assign	elip_bus_ram.rstn = clk_rst.rstn;

	assign	jtag_bus.addr = '0;
	assign	jtag_bus.rd = 1'b0;
	assign	jtag_bus.wr = 1'b0;
	assign	jtag_bus.data_write = '0;
	assign  jtag_bus.clk = 1'b0;
	assign  jtag_bus.rstn = 1'b0;
	assign	elip_bus_jtag.data_read = jtag_dr_read;
	assign	elip_bus_jtag.ready = 1'b1;
	assign	elip_bus_jtag.clk = clk_rst.clk;
	assign	elip_bus_jtag.rstn = clk_rst.rstn;

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
		set_por();
		->reset_ecc_flags;
		_wait(16);
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
		return errors;
	endfunction
	
	task _wait(input int wait_cycles=2);
		wait_for_n_clocks(wait_cycles);
	endtask
	/*###   FORCE SRAM BIT ERRORS   ############################################*/
	function void force_sram_input_data(logic[SRAM_WIDTH-1:0] value);
		force `SRAM_INST.D = value;
	endfunction
	
	function void release_sram_input_data();
		release `SRAM_INST.D;
	endfunction
	
	/*###   FORCE SRAM ADDR ERRORS   ###########################################*/
	function void force_sram_address(logic[SRAM_ADDR_WIDTH-1:0] address);
		force `SRAM_INST.A = address;
	endfunction
	
	function void release_sram_address();
		release `SRAM_INST.A;
	endfunction

	/*###   tasks   ######################################################*/
	task automatic read_ram(input shortint address, output shortint data, output ecc_t ecc);
		elip_read_seq	ram_seq = new();
		ram_seq.address = address;
		ram_seq.start(elip_sequencer);
		data = ram_seq.data[15:0];
		ecc  = ram_seq.ecc[5:0];
		#2ns;
	endtask

	function automatic void generate_ecc_error(elip_write_seq seq, error_t error_type);
		random_ecc_error	error;
		error = new(seq.data, seq.ecc, error_type);
		error.randomize();
		seq.data = error.get_data();
		seq.ecc = error.get_ecc();
//		`INFO($sformatf("altered bits: data: %4h\t\t ecc: %3h", error.data_changer, error.ecc_changer));
	endfunction
	
	/*###   tasks   ######################################################*/
	task automatic write_ram(input shortint address, input shortint data);
		elip_write_seq  ram_seq = new();
		ram_seq.address = address;
		ram_seq.data = data;
		ram_seq.ecc  = DWF_ecc_gen_chkbits(16, 6, data);
		ram_seq.start(elip_sequencer);
		#2ns;
	endtask
	
	/*###   TEST CASES   ######################################################*/
	task automatic elip_write_ram_with_(error_t error);
		shortint ram_address;
		shortint data;
		shortint ecc;
		shortint exp_data[$];
		shortint exp_ecc[$];
		for (ram_address = 0; ram_address < LENGTH_OF_SRAM; ram_address++) begin
			exp_data.push_back($urandom);
			exp_ecc.push_back(DWF_ecc_gen_chkbits(16, 6, exp_data[ram_address]));
			begin
				elip_write_seq  ram_seq = new();
				ram_seq.address = ram_address;
				ram_seq.data = exp_data[ram_address];
				ram_seq.ecc  = DWF_ecc_gen_chkbits(16, 6, exp_data[ram_address]);
				generate_ecc_error(ram_seq, error);
				ram_seq.start(elip_sequencer);
				if (error == TWO_BIT_ERR) begin  
					exp_data[ram_address] = ram_seq.data; //save since nothing is corrected
					exp_ecc[ram_address] = DWF_ecc_gen_chkbits(16, 6, exp_data[ram_address]);
				end
				#2ns;
			end
			_wait(1);
			`FAIL_UNLESS_EQUAL(ecc_fail_reg, (error == TWO_BIT_ERR) ? 1'b1 : 1'b0)
			`FAIL_UNLESS_EQUAL(ecc_corr_reg, (error == NO_BIT_ERR) ? 1'b0 : 1'b1)
			_wait(1); 
			->reset_ecc_flags;
		end
		for (ram_address = 0; ram_address < LENGTH_OF_SRAM; ram_address++) begin
			read_ram(ram_address, data, ecc);
			_wait(1);
			`FAIL_UNLESS_EQUAL(data, exp_data[ram_address])
			`FAIL_UNLESS_EQUAL(ecc, exp_ecc[ram_address])
			`FAIL_UNLESS_EQUAL(ecc_fail_reg, 1'b0)
			`FAIL_UNLESS_EQUAL(ecc_corr_reg, 1'b0)
			_wait(1); 
			->reset_ecc_flags;
		end
	endtask
	
	task automatic write_sram_with_(error_t error_type);
		shortint ram_address;
		shortint data;
		shortint ecc;
		shortint exp_data[$];
		shortint exp_ecc;
		logic[SRAM_WIDTH-1:0] sram_data;
		
		for (ram_address = 0; ram_address < LENGTH_OF_SRAM; ram_address++) begin
			random_sram_data_error	error;
			exp_data.push_back($urandom);
			get_sram_data(exp_data[ram_address], ram_address, sram_data);
				
			error = new(sram_data, error_type);
			error.randomize();
			force_sram_input_data(error.get_data());
			if (error_type == TWO_BIT_ERR)
				exp_data[ram_address] = error.get_data();
				
			write_ram(ram_address, exp_data[ram_address]);
			_wait(1);
			`FAIL_UNLESS_EQUAL(ecc_fail_reg, 1'b0)
			`FAIL_UNLESS_EQUAL(ecc_corr_reg, 1'b0)
			release_sram_input_data();
			_wait(1); 
			->reset_ecc_flags;
		end
		for (ram_address = 0; ram_address < LENGTH_OF_SRAM; ram_address++) begin
			exp_ecc = DWF_ecc_gen_chkbits(16, 6, exp_data[ram_address]);
			read_ram(ram_address, data, ecc);
			_wait(1);
			`FAIL_UNLESS_EQUAL(data, exp_data[ram_address])
			`FAIL_UNLESS_EQUAL(ecc, exp_ecc)
			`FAIL_UNLESS_EQUAL(ecc_fail_reg, (error_type == TWO_BIT_ERR) ? 1'b1 : 1'b0)
			`FAIL_UNLESS_EQUAL(ecc_corr_reg, (error_type == ONE_BIT_ERR) ? 1'b1 : 1'b0)
			_wait(1); 
			->reset_ecc_flags;
		end
	endtask
	
	task automatic generate_address_error_with_(error_t error_type);
		shortint ram_address;
		shortint data;
		shortint ecc;
		shortint exp_data[$];
		shortint exp_ecc;
		logic[SRAM_WIDTH-1:0] sram_data;
		
		
		for (ram_address = 0; ram_address < LENGTH_OF_SRAM; ram_address++) begin
			random_sram_address_error	error;
			exp_data.push_back($urandom);
				
			error = new(ram_address, error_type);
			error.randomize();
			force_sram_address(error.get_data());
			
			write_ram(ram_address, exp_data[ram_address]);
			_wait(1);
			`FAIL_UNLESS_EQUAL(ecc_fail_reg, 1'b0)
			`FAIL_UNLESS_EQUAL(ecc_corr_reg, 1'b0)
			release_sram_address();
			_wait(1); 
			->reset_ecc_flags;
			
			exp_ecc = DWF_ecc_gen_chkbits(16, 6, exp_data[ram_address]);
			read_ram(error.get_data(), data, ecc);
			_wait(1);
			`FAIL_UNLESS_EQUAL(data, exp_data[ram_address])
			`FAIL_UNLESS_EQUAL(ecc, exp_ecc)
			
			//FIXME: depending on P52143-251 have uncorrectable bit errors for both
			`FAIL_UNLESS_EQUAL(ecc_fail_reg, (error_type == NO_BIT_ERR) ? 1'b0 : 1'b1)
			`FAIL_UNLESS_EQUAL(ecc_corr_reg, (error_type == ONE_BIT_ERR) ? 1'b0 : 1'b0)
			_wait(1); 
			->reset_ecc_flags;
		end
	endtask
	
	
	
	`SVUNIT_TESTS_BEGIN
		enable_clk = 1'b1;
		#10us;
		jtag_sequencer = _top_config._elip_jtag_agent.m_sequencer;
		elip_sequencer = _top_config._elip_ram_agent.m_sequencer;
	
		`SVTEST ($sformatf("check RAM content and ecc flag after valid write access"))
			elip_write_ram_with_(NO_BIT_ERR);
		`SVTEST_END
	
		`SVTEST ($sformatf("Generate 1 Bit ECC error on ELIP interface - data_write and check ECC correction"))
			elip_write_ram_with_(ONE_BIT_ERR);
		`SVTEST_END
	
		`SVTEST ($sformatf("Generate 2 Bit ECC error on ELIP interface - data_write and check ECC fail"))
			elip_write_ram_with_(TWO_BIT_ERR);
		`SVTEST_END
	
		`SVTEST ($sformatf("Generate 1 Bit ECC error in RAM data - check ECC correction"))
			write_sram_with_(ONE_BIT_ERR);
		`SVTEST_END
	
		`SVTEST ($sformatf("Generate 2 Bit ECC error in RAM data - check ECC fail"))
			write_sram_with_(TWO_BIT_ERR);
		`SVTEST_END
	
		`SVTEST ($sformatf("Generate 1 Bit error in RAM address by write access - check ECC fail"))
			generate_address_error_with_(ONE_BIT_ERR);
		`SVTEST_END
	
		`SVTEST ($sformatf("Generate 2 Bit error in RAM address by write access - check ECC fail"))
			generate_address_error_with_(TWO_BIT_ERR);
		`SVTEST_END
		
		enable_clk = 1'b0;
	`SVUNIT_TESTS_END

endmodule
