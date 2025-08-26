/**
 * Module: jtag_tap
 * 
 * JTAG tap module for instruction / data word shifting and JTAG FSM 
 */
module jtag_tap import jtag_pkg::*; (
		jtag_status_if.master	status,
		jtag_pad_if.slave		pads,
		input	logic 			i_atpgmode,
		input	logic			i_tdo_unlatched,
		input	logic			i_tdo_latched,
		input	logic			i_dsr2tdo,
		input	t_jtag_dsr		i_dr
	);
	
	jtag_tap_states	tap_state, tap_state_nxt;
	t_jtag_isr		ir_register, ir_shiftregister;
	t_jtag_dsr		dr_shiftregister;
	
	logic			tdo_latch;
	
	logic			update_dr, capture_dr, shift_dr;
	logic			update_ir, capture_ir, shift_ir;
	logic			run_idle, test_rst;
	logic			update_dr_fe, update_ir_fe, capture_dr_fe, shift_dr_fe, run_idle_fe, test_rst_fe;
	
	//---------------------------------------------------
  	// Tap state machine
	always_ff@(negedge pads.trstn, posedge pads.tck) begin
		if (pads.trstn == 1'b0) begin
			tap_state <= TS_RESET;
		end
		else begin
			tap_state <= tap_state_nxt;
		end
	end
	
	always_comb begin
		tap_state_nxt = tap_state;
		case (tap_state)
			TS_RESET: begin
				if (pads.tms == 1'b0)
					tap_state_nxt = TS_RUN;
			end
			TS_RUN: begin
				if (pads.tms == 1'b1)
					tap_state_nxt = TS_SELECT_DR;
			end
			TS_SELECT_DR: begin
				if (pads.tms == 1'b1)
					tap_state_nxt = TS_SELECT_IR;
				else
					tap_state_nxt = TS_CAPTURE_DR;
			end
			TS_SELECT_IR: begin
				if (pads.tms == 1'b1)
					tap_state_nxt = TS_RESET;
				else
					tap_state_nxt = TS_CAPTURE_IR;
			end
			TS_CAPTURE_DR: begin
				if (pads.tms == 1'b1)
					tap_state_nxt = TS_EXIT1_DR;
				else
					tap_state_nxt = TS_SHIFT_DR;
			end
			TS_SHIFT_DR: begin
				if (pads.tms == 1'b1)
					tap_state_nxt = TS_EXIT1_DR;
			end
			TS_EXIT1_DR: begin
				if (pads.tms == 1'b1)
					tap_state_nxt = TS_UPDATE_DR;
				else
					tap_state_nxt = TS_PAUSE_DR;
			end
			TS_PAUSE_DR: begin
				if (pads.tms == 1'b1)
					tap_state_nxt = TS_EXIT2_DR;
			end
			TS_EXIT2_DR: begin
				if (pads.tms == 1'b1)
					tap_state_nxt = TS_UPDATE_DR;
				else
					tap_state_nxt = TS_SHIFT_DR;
			end
			TS_UPDATE_DR: begin
				if (pads.tms == 1'b1)
					tap_state_nxt = TS_SELECT_DR;
				else
					tap_state_nxt = TS_RUN;
			end
			TS_CAPTURE_IR: begin
				if (pads.tms == 1'b1)
					tap_state_nxt = TS_EXIT1_IR;
				else
					tap_state_nxt = TS_SHIFT_IR;
			end
			TS_SHIFT_IR: begin
				if (pads.tms == 1'b1)
					tap_state_nxt = TS_EXIT1_IR;
			end
			TS_EXIT1_IR: begin
				if (pads.tms == 1'b1)
					tap_state_nxt = TS_UPDATE_IR;
				else
					tap_state_nxt = TS_PAUSE_IR;
			end
			TS_PAUSE_IR: begin
				if (pads.tms == 1'b1)
					tap_state_nxt = TS_EXIT2_IR;
			end
			TS_EXIT2_IR: begin
				if (pads.tms == 1'b1)
					tap_state_nxt = TS_UPDATE_IR;
				else
					tap_state_nxt = TS_SHIFT_IR;
			end
			TS_UPDATE_IR: begin
				if (pads.tms == 1'b1)
					tap_state_nxt = TS_SELECT_DR;
				else
					tap_state_nxt = TS_RUN;
			end
			default: begin
				tap_state_nxt = TS_RESET;
			end
		endcase
	end
	
	//-------------------------------------------
	// Tap state decoding
	always_comb begin
		update_ir 	= (tap_state == TS_UPDATE_IR	) ? 1'b1 : 1'b0;
		update_dr 	= (tap_state == TS_UPDATE_DR	) ? 1'b1 : 1'b0;
		capture_ir 	= (tap_state == TS_CAPTURE_IR	) ? 1'b1 : 1'b0;
		capture_dr 	= (tap_state == TS_CAPTURE_DR	) ? 1'b1 : 1'b0;
		shift_ir 	= (tap_state == TS_SHIFT_IR		) ? 1'b1 : 1'b0;
		shift_dr 	= (tap_state == TS_SHIFT_DR		) ? 1'b1 : 1'b0;
		test_rst 	= (tap_state == TS_RESET		) ? 1'b1 : 1'b0;
		run_idle 	= (tap_state == TS_RUN			) ? 1'b1 : 1'b0;
	end
	
	
	// TODO: Missing: reset of IR and DR when in test_rst...
	
	//-------------------------------------------
	// IR & DR shift registers + IR register
	always_ff @(posedge pads.tck or negedge pads.trstn) begin
		if (pads.trstn == 1'b0)  begin
			// instruction register
			ir_register		 <= '0;
			ir_shiftregister <= '0;
			// data shift register
			dr_shiftregister <= '0;
		end
		else begin
			// instruction register
			if (update_ir == 1'b1)	// update IR from shift register
				ir_register <= ir_shiftregister;
			if (capture_ir == 1'b1)	// capture IR to be shifted out
				ir_shiftregister[1:0] <= 2'b01;
			if (shift_ir == 1'b1)	// shifting IR -> left cat TDI + right shift
				ir_shiftregister <= {pads.tdi, ir_shiftregister[7:1]};
			
			// data shift register
			if (capture_dr == 1'b1)	// capture data to be shifted out
				dr_shiftregister <= i_dr;
			if (shift_dr == 1'b1)	// shifting DR
				dr_shiftregister <= {pads.tdi, dr_shiftregister[$left(dr_shiftregister):1]};
		end
	end
	
	//-------------------------------------------
	// Latched tap state decoding
	always_ff @(negedge pads.tck or negedge pads.trstn) begin
		if (pads.trstn == 1'b0)  begin
			update_dr_fe	<= 1'b0;
			update_ir_fe	<= 1'b0;
			shift_dr_fe		<= 1'b0;
			capture_dr_fe	<= 1'b0;
			test_rst_fe		<= 1'b1;
			run_idle_fe		<= 1'b0;
		end
		else begin
			update_dr_fe 	<= update_dr;
			update_ir_fe	<= update_ir;
			shift_dr_fe		<= shift_dr;
			capture_dr_fe	<= capture_dr;
			test_rst_fe		<= test_rst;
			run_idle_fe		<= run_idle;
		end
	end
	
	//-------------------------------------------
	// TDO latch
	always_ff @(negedge pads.tck or negedge pads.trstn) begin
		if (pads.trstn == 1'b0)  begin
			tdo_latch <= 1'b0;
		end
		else begin
			tdo_latch <= (i_tdo_latched | (ir_shiftregister[0] & shift_ir) | (i_dsr2tdo & shift_dr & dr_shiftregister[0]));
		end
	end
	
	//-------------------------------------------
	// create JTAG bus
	assign status.capture_dr	= capture_dr;
	assign status.test_rst	= test_rst;
	assign status.shift_dr	= shift_dr;
	assign status.run_idle	= run_idle;
	assign status.update_dr	= update_dr;
	assign status.update_ir	= update_ir;
	
	assign status.ir			= ir_register;
	
	assign status.test_rst_fe	= (i_atpgmode == 1'b0) ? test_rst_fe : 1'b0;
	assign status.run_idle_fe	= run_idle_fe;
	assign status.capture_dr_fe = capture_dr_fe;
	assign status.shift_dr_fe	= shift_dr_fe;
	assign status.update_dr_fe = update_dr_fe;
	assign status.update_ir_fe = update_ir_fe;

	assign	status.dsr			= (capture_dr == 1'b0) ? dr_shiftregister : '0;
	
	assign	pads.tdo			= (tdo_latch | i_tdo_unlatched);

endmodule : jtag_tap


