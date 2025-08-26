`include "svunit_defines.svh"

class randc_wrapper;
	randc	logic[11:0]	value;
	function logic[11:0] get_new_value();
		this.randomize();
		return this.value;
	endfunction
endclass

module main_fsm_test import project_pkg::*; ();
	
	`include "uvm_macros.svh"
	
	import svunit_pkg::svunit_testcase;
	import svunit_uvm_mock_pkg::*;
	import addresses_pkg::*;
	import common_test_pkg::*;
	import uvm_pkg::*;
	import unit_test_pkg::*;
	import common_env_pkg::*;
	import main_control_pkg::*;
	import elip_bus_pkg::*;

	string name = "main_fsm_test";
	svunit_testcase svunit_ut;
	
	//===================================
	// This is the UUT that we're 
	// running the Unit Tests on
	//===================================
	`clk_def(27777ps)
	
	`tick_gen
	
	top_config	_top_config;
	check_elip	_check_elip;
	
	randc_wrapper	otp_address_to_read;
	
	elip_bus_sequencer_t	elip_sequencer;
	
	/*###   interface definitions   ######################################################*/
	otp_io_if		otp_io ();
	otp_ip_bus_if #(12, 12) otp_ip_bus ();
	elip_full_if	elip ();
	elip_bus_if		elip_bus();

	elip_if #(.addr_width(16), .data_width(16)) elip_registers();
	elip_bus_if		elip_bus_registers();
	data_t			o_elip_register_read;
	
	ecc_error_if #(1) ecc_error ();
	
	/*###   DSI3 block instance   ######################################################*/
	logic	vcc_ok, enable_transceivers, ldo_ok, ignore_uv, ignore_vrr_uv, rfc, enable_ldo, vrr_ok;
	logic	main_fsm_fail;
	
	logic initializing;
	main_fsm i_main_fsm (
		.clk_rst                (clk_rst.slave         ), 
		.elip                   (elip.master           ), 
		.elip_registers         (elip_registers.slave  ),
		.i_vrr_ok               (vrr_ok                ),
		.i_vcc_ok               (vcc_ok                ), 
		.i_ldo_ok               (ldo_ok                ),
		.i_ignore_ldo_uv        (ignore_uv             ),
		.i_ignore_hwf           (ignore_vrr_uv         ),
		.i_tick_1us             (tick_1us              ),  
		.o_enable_transceivers  (enable_transceivers   ),
		.otp_ip_bus             (otp_ip_bus.master     ),
		.o_otp_ehv              (otp_io.a_ehv          ),
		.o_rfc                  (rfc                   ),
		.o_enable_ldo           (enable_ldo            ),
		.ecc_error              (ecc_error.master      ), 
		.o_main_fsm_fail        (main_fsm_fail         ),
		.o_elip_out             (o_elip_register_read  ),
		.o_initializing         (initializing          )
	);
	
	interface_converter_elip_bus_2_elip #(.data_width  (16 )) i_interface_converter_registers (
			.clk_rst     (clk_rst.slave    ), 
			.elip_bus    (elip_bus_registers   ), 
			.elip        (elip_registers.master       ), 
			.i_data_out  (o_elip_register_read ));
	
	test_top i_test_top (
		.clk_rst     (clk_rst    ), 
		.otp_io      (otp_io     ), 
		.otp_ip_bus  (otp_ip_bus ));
	
	interface_converter_elip_full_2_elip_bus i_interface_converter_elip (
			.clk_rst    (clk_rst.slave             ),
			.elip_full  (elip.slave ), 
			.elip_bus   (elip_bus  ));
	
	ram_model #(
		.RAM_SIZE  (1<<16 )
	) i_command_buffer_model (
		.clk_rst   (clk_rst.slave  ), 
		.elip      (elip.slave     )
	);
	
	/*###   start simulation   ######################################################*/
	initial begin
		_top_config = new("_top_config");
		
		uvm_config_db #(top_config)::set(null, "uvm_test_top", "_top_config", _top_config);
		uvm_config_db #(top_config)::set(null, "uvm_test_top.m_env", "_top_config", _top_config);
		_top_config._elip_config.vif		= elip_bus;
		_top_config._elip_register_config.vif = elip_bus_registers;
		
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
		if(_check_elip == null) _check_elip = _top_config._check_elip;
		set_otp_data("otp_test.dat");
		otp_address_to_read = new();
		vcc_ok = 1'b0;
		vrr_ok = 1'b0;
		ignore_uv = 1'b0;
		ignore_vrr_uv = 1'b0;
		ldo_ok = 1'b0;
		set_por();
		#1us;
		enable_clk = 1'b1;
	endtask

	//===================================
	// Here we deconstruct anything we 
	// need after running the Unit Tests
	//===================================
	task teardown();
		enable_clk = 1'b0;
		svunit_ut.teardown();
	endtask
	
	function automatic int get_errors();
		int errors;
		errors += _check_elip.get_error_count();
		errors += (!uvm_report_mock::verify_complete()) ? 1 : 0;
		return errors;
	endfunction
	
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
	
	task set_otp_data(string file_name);
		testrunner.ts.ut.i_test_top.i_otp_wrapper.U_OTPWRAP_L3_TOP.U_OTPWRAP_L2_CPU.U_OTPWRAP_L1_JTAG.U_OTPWRAP_L0_ATPG.GEN_TSMC.U_OTP4KX12.u_otp4kx12.readOtp(2048'(file_name));
		_check_elip.initialize(file_name);
	endtask
	
	localparam time wait_after_trimming = 40us;
	localparam time time_for_OTP_read_out = 400us;
	localparam time time_for_initializing_RAM = 200us;
	
	localparam time	time_for_startup = (wait_after_trimming + time_for_OTP_read_out + time_for_initializing_RAM);
	
	
	/*###   other tasks   ######################################################*/
	data_t			read_data;
	SPI_IRQ_STAT_t	stat;
	
	task _wait(input int wait_cycles=2);
		wait_for_n_clocks(wait_cycles);
	endtask
	
	task automatic read_elip (input elip_addr_t address, output data_t data);
		elip_bus_seq	seq = new();
		elip_tr			tr = new();
		tr.randomize with {write == 1'b0; address == local::address;};
		seq.req= tr;
		seq.start(elip_sequencer);
		data = seq.req.data_read;
	endtask
	
	task automatic write_elip(input elip_addr_t address, input data_t data);
		elip_bus_seq	seq = new();
		elip_tr			tr = new();
		tr.randomize with {write == 1'b1; address == local::address; data_write == local::data;};
		seq.req= tr;
		seq.start(elip_sequencer);
	endtask
	
	task automatic read_status();
		read_elip(ADDR_SPI_SPI_IRQ_STAT, read_data);
		stat = read_data;
	endtask
	
	/*###   test cases   ######################################################*/
	`SVUNIT_TESTS_BEGIN
	begin
		#1us;
		elip_sequencer = _top_config._elip_register_agent.m_sequencer;
		
		`SVTEST("check startup - stay at waiting for VCC OK")
			_check_elip.expect_no_access();
			#300us;
			repeat (10) begin
				#10us;
				`FAIL_IF_LOG(i_main_fsm.state != WAIT_FOR_VCC_OK, $sformatf("state=%s", i_main_fsm.state.name()))
			end
			`FAIL_IF_EQUAL(enable_transceivers, 1'b1)
			`FAIL_UNLESS_EQUAL(enable_ldo, 1'b0)
			`FAIL_UNLESS_EQUAL(rfc, 1'b0)
			`FAIL_UNLESS_EQUAL(get_errors(), 0)
		`SVTEST_END
			
		`SVTEST("check startup for VCC OK")
			#300us;
			`FAIL_IF_LOG(i_main_fsm.state != WAIT_FOR_VCC_OK, $sformatf("state=%s", i_main_fsm.state.name()))
			`FAIL_UNLESS_EQUAL(initializing, 1'b0)
			vcc_ok = 1'b1;
			wait_for_n_clocks(2);
			`FAIL_IF_EQUAL(i_main_fsm.state, WAIT_FOR_VCC_OK)
		`SVTEST_END
		
		`SVTEST("check startup for VRR OK")
			#300us;
			vcc_ok = 1'b1;
			wait_for_n_clocks(2);
			`FAIL_IF_LOG(i_main_fsm.state != WAIT_FOR_VRR_OK, $sformatf("state=%s", i_main_fsm.state.name()))
			`FAIL_UNLESS_EQUAL(initializing, 1'b0)
			vrr_ok = 1'b1;
			wait_for_n_clocks(2);
			`FAIL_IF_EQUAL(i_main_fsm.state, WAIT_FOR_VRR_OK)
		`SVTEST_END
		
		`SVTEST("check startup - stay at waiting for LDO OK")
			vcc_ok = 1'b1;
			vrr_ok = 1'b1;
			#(time_for_startup);
			repeat (10) begin
				#10us;
				`FAIL_UNLESS_EQUAL(i_main_fsm.state, WAIT_FOR_LDO_OK)
				`FAIL_UNLESS_EQUAL(enable_transceivers, 1'b0)
				`FAIL_UNLESS_EQUAL(rfc, 1'b0)
				`FAIL_UNLESS_EQUAL(enable_ldo, 1'b1)
				`FAIL_UNLESS_EQUAL(initializing, 1'b0)
			end
			ldo_ok = 1'b1;
			#10us;
			`FAIL_UNLESS_EQUAL(enable_ldo, 1'b1)
			`FAIL_UNLESS_EQUAL(rfc, 1'b1)
			`FAIL_UNLESS_EQUAL(enable_transceivers, 1'b1)
			`FAIL_UNLESS_EQUAL(get_errors(), 0)
		`SVTEST_END
			
		`SVTEST("check startup - finished")
			vcc_ok = 1'b1;
			vrr_ok = 1'b1;
			ldo_ok = 1'b1;
			#(time_for_startup);
			`FAIL_UNLESS_EQUAL(enable_ldo, 1'b1)
			`FAIL_UNLESS_EQUAL(i_main_fsm.state, POWERED_UP)
			`FAIL_UNLESS_EQUAL(enable_transceivers, 1'b1)
			`FAIL_UNLESS_EQUAL(rfc, 1'b1)
			`FAIL_UNLESS_EQUAL(initializing, 1'b0)
			`FAIL_UNLESS_EQUAL(get_errors(), 0)
		`SVTEST_END
			
		`SVTEST("check no RAM init when VCC in UV")
			vcc_ok = 1'b0;
			vrr_ok = 1'b1;
			_check_elip.expect_no_access();
			fork
				#1ms;
				begin
					@(elip.wr or elip.rd or elip.ready);
					`FAIL_UNLESS_EQUAL(elip.wr, 1'b0)
					`FAIL_UNLESS_EQUAL(elip.ready, 1'b1)
					`FAIL_UNLESS_EQUAL(elip.rd, 1'b0)
				end
			join_any
			disable fork;
			`FAIL_UNLESS_EQUAL(get_errors(), 0)
		`SVTEST_END
		
		`SVTEST("check ignore UV")
			vcc_ok = 1'b1;
			vrr_ok = 1'b1;
			#(time_for_startup);
			`FAIL_UNLESS_EQUAL(i_main_fsm.state, WAIT_FOR_LDO_OK)
			`FAIL_UNLESS_EQUAL(enable_transceivers, 1'b0)
			`FAIL_UNLESS_EQUAL(rfc, 1'b0)
			`FAIL_UNLESS_EQUAL(enable_ldo, 1'b1)
			`FAIL_UNLESS_EQUAL(initializing, 1'b0)
			wait_for_n_clocks(2);
			ignore_uv = 1'b1;
			#10us;
			`FAIL_UNLESS_EQUAL(i_main_fsm.state, POWERED_UP)
			`FAIL_UNLESS_EQUAL(enable_transceivers, 1'b1)
			`FAIL_UNLESS_EQUAL(rfc, 1'b1)
			`FAIL_UNLESS_EQUAL(get_errors(), 0)
			`FAIL_UNLESS_EQUAL(enable_ldo, 1'b1)
		`SVTEST_END	
		
		`SVTEST("check ignore HWF")
			vcc_ok = 1'b0;
			vrr_ok = 1'b0;
			#300us;
			`FAIL_IF_LOG(i_main_fsm.state != WAIT_FOR_VCC_OK, $sformatf("state=%s", i_main_fsm.state.name()))
			ignore_vrr_uv = 1'b1;
			wait_for_n_clocks(2);
			`FAIL_IF_EQUAL(i_main_fsm.state, WAIT_FOR_VCC_OK)
			`FAIL_IF_EQUAL(i_main_fsm.state, WAIT_FOR_VRR_OK)
		`SVTEST_END	
		
		`SVTEST("check applicative OTP readout")
			vcc_ok = 1'b1;
			vrr_ok = 1'b1;
			#(time_for_startup);
			for (int loop=0; loop<100; loop++) begin
				int	data;
				write_elip(ADDR_OTP_CTRL_OTP_READ_ADDRESS, otp_address_to_read.get_new_value());
				#5us;
				read_elip(ADDR_OTP_CTRL_OTP_READ_VALUE, data);
				`FAIL_UNLESS_EQUAL(get_errors(), 0)
			end
		`SVTEST_END
			
		`SVTEST("check applicative OTP readout - initial status")
			OTP_READ_STATUS_t	status;
			#10us;
			read_elip(ADDR_OTP_CTRL_OTP_READ_STATUS, status);
			`FAIL_UNLESS_EQUAL(status.STATUS, main_control_pkg::INITIAL)
		`SVTEST_END
		
		`SVTEST("check applicative OTP readout - status READING")
			OTP_READ_STATUS_t	status;
			int	data;
			vrr_ok = 1'b1;
			vcc_ok = 1'b1;
			#(time_for_startup);
			write_elip(ADDR_OTP_CTRL_OTP_READ_ADDRESS, otp_address_to_read.get_new_value());
			read_elip(ADDR_OTP_CTRL_OTP_READ_STATUS, status);
			#10us;
			`FAIL_UNLESS_EQUAL(status.STATUS, main_control_pkg::READING)
			`FAIL_UNLESS_EQUAL(get_errors(), 0)
		`SVTEST_END
		
		`SVTEST("check applicative OTP readout - status FINISHED")
			OTP_READ_STATUS_t	status;
			int	data;
			vrr_ok = 1'b1;
			vcc_ok = 1'b1;
			#(time_for_startup);
			write_elip(ADDR_OTP_CTRL_OTP_READ_ADDRESS, otp_address_to_read.get_new_value());
			#20us;
			read_elip(ADDR_OTP_CTRL_OTP_READ_STATUS, status);
			#10us;
			`FAIL_UNLESS_EQUAL(status.STATUS, main_control_pkg::FINISHED)
			`FAIL_UNLESS_EQUAL(get_errors(), 0)
		`SVTEST_END
		
		
		`SVTEST("check applicative OTP readout - status FAIL")
			OTP_READ_STATUS_t	status;
			int	data;
			vcc_ok = 1'b1;
			vrr_ok = 1'b1;
			repeat(2) begin
				#150us;
				write_elip(ADDR_OTP_CTRL_OTP_READ_ADDRESS, otp_address_to_read.get_new_value());
				#20us;
				read_elip(ADDR_OTP_CTRL_OTP_READ_STATUS, status);
				#10us;
				`FAIL_UNLESS_EQUAL(status.STATUS, main_control_pkg::FAIL)
			end
			#200us;
			`FAIL_UNLESS_EQUAL(get_errors(), 0)
		`SVTEST_END
		
		`SVTEST("check initializing flag")
			vcc_ok = 1'b1;
			vrr_ok = 1'b1;
			ldo_ok = 1'b1;
			fork
				begin
					@(i_main_fsm.state);
					case (i_main_fsm.state)
						RESET, WAIT_FOR_VCC_OK, WAIT_FOR_VRR_OK,
								WAITING_AFTER_TRIMMING, 
								WAIT_FOR_LDO_OK,
								POWERED_UP: begin
									`FAIL_UNLESS_EQUAL(initializing, 1'b0)
							end
						RAM_ZEROING, READ_HIGH_ADDRESS, READ_LOW_ADDRESS,
								CHECK_ADDRESS,
								READ_HIGH_DATA, READ_LOW_DATA,
								PREPARE_WRITE_DATA, WRITE_DATA
								: begin
							`FAIL_UNLESS_EQUAL(initializing, 1'b1)
					end
					endcase
				end
				begin
					#2ms;
				end
				
			join_any
			disable fork;
		`SVTEST_END
		
	end	 
	`SVUNIT_TESTS_END
	
endmodule
