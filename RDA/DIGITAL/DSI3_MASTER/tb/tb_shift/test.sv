`include "svunit_defines.svh"

package test_support;
	import dsi3_pkg::*;
	typedef enum {S_IDLE, S_PDCM, S_CRM} status_t;
	class dsi3_channel;
		virtual dsi3_start_request_if	request;
		virtual dsi3_common_config_if	common_config;
		virtual clk_reset_if 			clk_rst;
		virtual status_if 				status;
		
		int periods_to_be_done;
		
		bit busy;
		
		function new();
			busy = 1'b0;
		endfunction
		
		function void initialize();
			request.mode = MODE_PDCM;
			request.request = 1'b0;
			request.transmitting = 1'b0;
			status.status = S_IDLE;
		endfunction
		
		task do_crm();
			fork
				begin
					if (busy)
						@(negedge busy);
					busy = 1'b1;
					request.request = 1'b1;
					request.mode = MODE_CRM;
					@(posedge request.tick_transmit);
					status.status = S_CRM;
					@(posedge clk_rst.clk) #1;
					request.request = 1'b0;
					request.transmitting = 1'b1;
					#(295us*(1<<common_config.bit_time));
					request.transmitting = 1'b0;
					#(27us*(3+common_config.chip_time));
					status.status = S_IDLE;
					busy = 1'b0;
				end
			join_none
		endtask
		
		task do_pdcm(int periods);
			if (busy)
				@(negedge busy);
			busy = 1'b1;
			periods_to_be_done = periods;
			fork
				begin
					request.request = 1'b1;
					request.mode = MODE_PDCM;
					while (periods_to_be_done > 0) begin
						@(posedge request.tick_pdcm);
						periods_to_be_done--;
						status.status = S_PDCM;
						@(posedge clk_rst.clk) #1;
						request.request = 1'b0;
						request.transmitting = 1'b1;
						fork
							begin
								#((8<<(common_config.bit_time))*1us);
								request.transmitting = 1'b0;
							end
						join_none
						#((common_config.pdcm_period-5)*1us);
						if (periods_to_be_done > 0)
							request.request = 1'b1;
					end
					busy = 1'b0;
					status.status = S_IDLE;
				end
			join_none
		endtask
		
	endclass
endpackage

interface status_if();
	import test_support::*;
	status_t	status;
endinterface

module test;
	
	`include "uvm_macros.svh"
	import test_support::*;
	import project_pkg::*;
	import svunit_pkg::svunit_testcase;
	import dsi3_pkg::*;
	import common_test_pkg::*;

	string name = "shift_test";
	svunit_testcase svunit_ut;
	
	//===================================
	// This is the UUT that we're 
	// running the Unit Tests on
	//===================================
	`clk_def(27777ps)
	
	`tick_gen
	
	/*###   interface definitions   ######################################################*/
	dsi3_channel	channel[DSI_CHANNELS-1:0];
	dsi3_common_config_if	common_config ();
	dsi3_start_request_if	request[DSI_CHANNELS-1:0]();
	status_if 	status[DSI_CHANNELS-1:0]();
	status_t	_status[DSI_CHANNELS-1:0];
	
	synchronization_if	sync[DSI_CHANNELS-1:0]();
	
	pad_int_if			syncb_pad();
	
	dsi_logic_t	_request;
	dsi_logic_t	_transmitting;
	dsi_logic_t	_mode;
	dsi_logic_t	_acknowledge;
	
	dsi_logic_t	register_sync;
	dsi_logic_t	sync_error;
	
	logic syncb, syncb_synced;
	assign syncb_pad.in_a = syncb;
	
	generate
		genvar i;
		for (i=0; i< DSI_CHANNELS; i++) begin : generate_testbench_signals
			initial begin
				channel[i] = new();
				channel[i].request = request[i];
				channel[i].common_config = common_config;
				channel[i].clk_rst = clk_rst;
				channel[i].status = status[i];
			end
			assign	_status[i] = status[i].status;
		end
	endgenerate
	
	/*###      ######################################################*/
	
	/*###   DSI3 block instance   ######################################################*/
	dsi3_start_manager u_dsi3_start_manager (
		.clk_rst        (clk_rst.slave        ),
		.common_config  (common_config.slave  ),
		.request        (request.slave        ),
		.sync           (sync.slave           ),
		.syncb_pad      (syncb_pad.master     ),
		.i_register_sync(register_sync        ),
		.o_sync_error   (sync_error           ),
		.o_syncb        (syncb_synced                )
	);
	
	property p_syncb_sync;
		logic	value;
		disable iff (clk_rst.rstn == 1'b0)
		@(posedge clk_rst.clk) (1,value = syncb) |-> ##2 (syncb_synced == value);
	endproperty
	
	syncb_sync: assert property (p_syncb_sync);
	syncb_oe: assert property (@(posedge clk_rst.clk) ~syncb_pad.oe) else $error("syncb_pad.oe is not correct. Got %1b but expected %1b", syncb_pad.oe, 1'b0);
	syncb_pd: assert property (@(posedge clk_rst.clk) ~syncb_pad.pd) else $error("syncb_pad.pd is not correct. Got %1b but expected %1b", syncb_pad.oe, 1'b0);
	syncb_pu: assert property (@(posedge clk_rst.clk) ~syncb_pad.pu) else $error("syncb_pad.pu is not correct. Got %1b but expected %1b", syncb_pad.oe, 1'b0);

	/* =======   INPUTS   =======
	 * 
	 * register_sync
	 * 
	 * common_config:
	 * pdcm_period, bit_time, chip_time, sync_pdcm, tx_shift
	 * 
	 * request:
	 * mode, transmitting, request, pdcm_in_progress
	 * 
	 * sync:
	 * register, reset, channels_to_sync, waiting
	 * 
	 * =======   OUTPUTS  =======
	 * request:
	 * pdcm_period_running, tick_pdcm, tick_transmit, pdcm_receive_timeout
	 * 
	 * sync:
	 * armed, fire, currently_registered_channels
	 * 
	 */
	
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
		common_config.bit_time = BITTIME_8US;
		common_config.chip_time = 2'd0;
		common_config.pdcm_period = 16'd999;
		common_config.sync_pdcm = 1'b1;
		common_config.tx_shift = 8'd36;
		svunit_ut.setup();
		#1us;
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
	
	task _wait(int clocks);
		wait_for_n_clocks(clocks);
	endtask
	
	`SVUNIT_TESTS_BEGIN
	begin
		#1;
		for(int i=0; i < DSI_CHANNELS; i++)
			channel[i].initialize();
		#1us;
		shift_crm();
		unsync_pdcm();
		shift_pdcm();
		
		sync_pdcm();

		apply_shift_while_in_pdcm();
		mixed_starts();
		mix_starts_of_crm();
	end	 
	`SVUNIT_TESTS_END
	
	task automatic unsync_pdcm();
		`SVTEST("unsync PDCM")
			common_config.sync_pdcm = 1'b0;
			_wait(2);
			for (int i=0; i< DSI_CHANNELS; i++) begin
				channel[i].do_pdcm(4);
				#700us;
			end
			#5ms;
		`SVTEST_END
	endtask
	
	task automatic sync_pdcm();
		`SVTEST("sync PDCM")
			_wait(2);
			for (int i=0; i< DSI_CHANNELS; i++) begin
				channel[i].do_pdcm(4);
				#700us;
			end
			#5ms;
		`SVTEST_END
		`SVTEST("sync PDCM - last is first")
			_wait(2);
			for (int i=DSI_CHANNELS-1; i>=0; i++) begin
				channel[i].do_pdcm(4);
				#700us;
			end
			#5ms;
		`SVTEST_END
	endtask
	
	task automatic shift_pdcm();
		for (int start_channel = 0; start_channel < DSI_CHANNELS; start_channel++) begin
			for (int shift = 0; shift <= 18*8/6; shift+=12) begin
				`SVTEST($sformatf("shift PDCM (unsynced) with channel %1d to %1d and shift = %3d", start_channel, DSI_CHANNELS-1, shift))
					common_config.tx_shift = 8'(shift);
					common_config.sync_pdcm = 1'b0;
					_wait(2);
					for (int i=start_channel; i< DSI_CHANNELS; i++) begin
						channel[i].do_pdcm(2);
					end
					#5ms;
				`SVTEST_END
				`SVTEST($sformatf("shift PDCM (synced) with channel %1d to %1d and shift = %3d", start_channel, DSI_CHANNELS-1, shift))
					common_config.tx_shift = 8'(shift);
					_wait(2);
					for (int i=start_channel; i< DSI_CHANNELS; i++) begin
						channel[i].do_pdcm(2);
					end
					#5ms;
				`SVTEST_END
			end
		end
	endtask
	
	task automatic apply_shift_while_in_pdcm();
		`SVTEST("apply shift while in PDCM")
		`SVTEST_END
	endtask
	
	task automatic shift_crm();
		for (int shift = 0; shift <= 18*8/6; shift+=12) begin
			`SVTEST($sformatf("shift CRM with shift = %3d", shift))
				common_config.tx_shift = 8'(shift);
				_wait(2);
				for (int i=0; i< DSI_CHANNELS; i++) begin
					channel[i].do_crm();
				end
				#3ms;
			`SVTEST_END
		end
	endtask
	
	task automatic mixed_starts();
		`SVTEST("mixed starts 1")
			channel[0].do_crm();
			channel[1].do_pdcm(1);
			channel[2].do_crm();
			channel[3].do_pdcm(1);
			#2ms;
		`SVTEST_END
		`SVTEST("mixed starts 2")
			channel[1].do_pdcm(1);
			#5us;
			channel[2].do_crm();
			#50us;
			channel[0].do_crm();
			#100us;
			channel[3].do_pdcm(1);
			#2ms;
		`SVTEST_END
	endtask
	
	task automatic mix_starts_of_crm();
		`SVTEST("mix starts of CRM")
		`SVTEST_END
	endtask
	
endmodule
