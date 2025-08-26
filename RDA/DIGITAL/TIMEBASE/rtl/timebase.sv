/**
 * Module: timebase
 * 
 * Module to adapt to external reference timing, do clock trimming & tick generation
 */
module timebase import project_pkg::*; #(
		parameter	base_addr = 0,
		parameter	addr_width = 16,
		parameter	DSI3_COUNT = 2
	) (
		clk_reset_if.slave 	clk_rst,							// system clock and corresponding reset
		clk_reset_if.slave	clkosc_rst,
		
		timebase_info_if.master	timebase_info,
		timebase_io_if.master	timebase_io,
		
		tmr_osc_if.master	tmr_osc,
		tmr_out_osc_if.master	tmr_out_osc,
		jtag_bus_if.slave	jtag_bus,
		output	jtag_dr_for_registers_t	o_jtag_dr,
		
		elip_if.slave		elip,
		output	elip_data_t	o_elip_data_read,
		
		input	dsi_logic_t	i_transmit_pending,
		
		clock_switch_if.timebase	clock_switch_io,
		
		input	logic		i_scanmode
	);
	
	import	common_lib_pkg::*;
	
	logic	tmr_dig_clk_auto_trim_en_tck;
	
	/*###   time base registers   ######################################################*/
	`include "time_base_registers_if_inst.sv"
	time_base_registers #(
		.base_addr                         (base_addr                               ), 
		.addr_width                        (addr_width                              )
	) i_time_base_registers (
		.clk_rst                           (clk_rst                                 ), 
		.addr                              (elip.addr                               ), 
		.data_in                           (elip.data_write                         ), 
		.wr                                (elip.wr                                 ), 
		.rd                                (elip.rd                                 ), 
		.data_out                          (o_elip_data_read                        ), 
		.time_base_registers_CLKREF_CONF   (time_base_registers_CLKREF_CONF.master  ), 
		.time_base_registers_TB_CNT        (time_base_registers_TB_CNT.master       ), 
		.time_base_registers_TRIM_OSC      (time_base_registers_TRIM_OSC.master     ), 
		.time_base_registers_TRIM_OSC_TCF  (time_base_registers_TRIM_OSC_TCF.master )
	);
	
	logic	clkref_ok, pll_locked;
	
	/*###   synchronization   ######################################################*/
	logic	test_auto_trim_en, clkpll_div_rising;
	sync #(
		.SIZE        (1       )
	) i_sync_auto_trim (
		.clk_rst     (clk_rst    ), 
		.i_in        (tmr_dig_clk_auto_trim_en_tck ), 
		.o_test_out  ( ), 
		.o_out       (test_auto_trim_en      )
	);
	
	sync_edge #(
		.SIZE        (1       ), 
		.EDGE        (1       )
	) i_sync_clkpll_div (
		.clk_rst     (clk_rst    ), 
		.i_in        (timebase_io.clkpll_div  ), 
		.o_test_out  (  ),
		.o_out       (       ), 
		.o_rising    (clkpll_div_rising   ), 
		.o_falling   ()
	);
	
	//*###   CLKREF dividing   ######################################################*/
	clkref_divider i_clkref_divider (
		.i_clkref      (timebase_io.clkref     ), 
		.i_rstn        (clk_rst.rstn       ), 
		.i_div_config  (time_base_registers_CLKREF_CONF.CLKREF_FREQ ), 
		.o_clkref_div  (timebase_io.clkref_div ));
	
	//*###   CLKREF synchronization   ######################################################*/
	logic	clkref_rising_osc, clkref_rising; 
	
	sync_edge #(
			.SIZE        (1       ), 
			.EDGE        (1       )
		) i_sync_clkref_osc (
			.clk_rst     (clkosc_rst    ), 
			.i_in        (timebase_io.clkref_div ), 
			.o_test_out  (        ), 
			.o_out       (        ), 
			.o_rising    (clkref_rising_osc   ), 
			.o_falling   (        ));
	
	sync_edge #(
			.SIZE        (1       ), 
			.EDGE        (1       )
		) i_sync_clkref (
			.clk_rst     (clk_rst ), 
			.i_in        (timebase_io.clkref_div  ), 
			.o_test_out  (        ), 
			.o_out       (        ), 
			.o_rising    (clkref_rising   ), 
			.o_falling   (        ));
	
	/*###   tick generation   ######################################################*/
	logic tick_3MHz;
	tick_gen #(
		.ratio     (6    )
	) i_tick_1_3us (
		.clk_rst   (clk_rst  ), 
		.reset_sync(1'b0 ), 
		.tick_out  (tick_3MHz));
	
	tick_div #(
		.ratio     (3    )
	) i_tick_1us (
		.clk_rst   (clk_rst  ), 
		.tick_in   (tick_3MHz), 
		.reset_sync(1'b0 ), 
		.tick_out  (timebase_info.tick_1us )
	);
	
	assign timebase_info.tick_1ms = (timebase_info.base_time[9:0] == '0) ? timebase_info.tick_1us : 1'b0;

	/*###   clkref & PLL monitor   ######################################################*/
	clkref_monitor #(
		.min_value      (33   ), 
		.max_value      (37   )	 
	) i_clkref_monitor (
		.clk_rst        (clk_rst       ),
		.clkosc_rst		(clkosc_rst		),
		.i_clkref_edge  (clkref_rising_osc ), 
		.o_clkref_ok    (clkref_ok   )
	);
	
	logic	pll_on;
	pll_monitor i_pll_monitor (
		.clk_rst         (clk_rst        ), 
		.i_clkref_rising (clkref_rising ), 
		.i_enable		 (pll_on),
		.i_clkpll_div_rising (clkpll_div_rising   ), 
		.o_pll_locked    (pll_locked   )
	);
	
	/*###   base time   ######################################################*/
	assign	time_base_registers_TB_CNT.CNT_in = time_base_registers_TB_CNT.CNT + 16'd1;
	assign	time_base_registers_TB_CNT.CNT_set = timebase_info.tick_1us;
	
	
	assign	timebase_info.base_time = time_base_registers_TB_CNT.CNT;
	
	//*###   connecting trim registers to output   ######################################################*/
	assign	timebase_io.trim_osc_f = time_base_registers_TRIM_OSC.TRIM_OSC;
	assign	timebase_io.trim_osc_tcf = time_base_registers_TRIM_OSC_TCF.TCF;
	
	/*###   time base FSM   ######################################################*/
	typedef enum logic[1:0] {NO_CLKREF, CLKREF_VALID, PLL_LOCKED, PLL_HOLD} timebase_state_enum;
	timebase_state_enum	state, state_nxt;
	
	logic	pll_hold, pll_hold_nxt, pll_on_nxt, clk_ok, clk_ok_nxt;
	logic[DSI3_COUNT-1:0]	transmission_pending_flags, transmission_pending_flags_nxt;
	
	always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0)  begin
			state		<= NO_CLKREF;
			pll_hold	<= 1'b0;
			pll_on	<= 1'b0;
			clk_ok		<= 1'b0;
			transmission_pending_flags <= '0;
		end
		else begin
			state		<= state_nxt;
			pll_hold	<= pll_hold_nxt;
			pll_on		<= pll_on_nxt;
			clk_ok		<= clk_ok_nxt;
			transmission_pending_flags <= transmission_pending_flags_nxt;
		end
	end
	
	assign	clock_switch_io.select_clock_pll = clk_ok;
	
	assign timebase_info.clkref_ok = clk_ok;
	
	always_comb begin : time_base_fsm_state_change
		state_nxt 		= state;
		pll_hold_nxt	= 1'b0;
		pll_on_nxt		= 1'b1;
		clk_ok_nxt		= 1'b0;
		transmission_pending_flags_nxt = '0;
		
		case (state) 
			NO_CLKREF : begin
				pll_on_nxt		= (pll_on == 1'b1) ? ~clock_switch_io.clock_switched : 1'b0;
				pll_hold_nxt	= (pll_hold == 1'b1) ? ~clock_switch_io.clock_switched : 1'b0;
				if (clkref_ok == 1'b1) begin
					state_nxt = CLKREF_VALID;
				end
			end
			CLKREF_VALID : begin
				pll_hold_nxt	= (pll_hold == 1'b1) ? ~clock_switch_io.clock_switched : 1'b0;
				if (pll_locked == 1'b1) begin
					state_nxt = PLL_LOCKED;
				end
				if (clkref_ok == 1'b0) begin
					state_nxt = NO_CLKREF;
				end
			end
			PLL_LOCKED : begin
				clk_ok_nxt = 1'b1;
				if ((clkref_ok == 1'b0) || (pll_locked == 1'b0)) begin
					if (i_transmit_pending != '0) begin
						transmission_pending_flags_nxt = i_transmit_pending;
						state_nxt = PLL_HOLD;
						pll_hold_nxt = 1'b1;
					end
					else begin
						clk_ok_nxt = 1'b0;	
						pll_hold_nxt = 1'b1;
						if (clkref_ok == 1'b0) begin
							state_nxt = NO_CLKREF;
						end
						else begin
							state_nxt = CLKREF_VALID;
						end
					end
				end
			end
			PLL_HOLD : begin
				pll_hold_nxt = 1'b1;
				clk_ok_nxt = 1'b1;
				transmission_pending_flags_nxt = i_transmit_pending & transmission_pending_flags;
				if (transmission_pending_flags == '0) begin
					clk_ok_nxt = 1'b0;
					if (clkref_ok == 1'b1) begin
						state_nxt = CLKREF_VALID;
					end
					else begin
						state_nxt 	= NO_CLKREF;
					end
				end
			end
		endcase
	end
	
	/*###   Test   ######################################################*/
	test_osc #(
		.BASE_ADDR                   (BASE_ADDR_TEST_OSC         ), 
		.ADDR_WIDTH                  (JTAG_IR_WIDTH              )
	) i_test_osc (
		.jtag_bus                    (jtag_bus                   ), 
		.o_jtag_dr                   (o_jtag_dr                  ), 
		.tmr_osc                     (tmr_osc                    ),  
		.i_PLL_ON_tmr_val            (pll_on                     ), 
		.o_PLL_ON_tmr_val            (timebase_io.pll_on         ), 
		.i_PLL_HOLD_tmr_val          (pll_hold                   ), 
		.o_PLL_HOLD_tmr_val          (timebase_io.pll_hold       ), 
		.o_tmr_dig_CLKSW_TST_EN      (clock_switch_io.test_en    ),
		.o_tmr_dig_CLKSW_TST_SEL     (clock_switch_io.test_sel   ),
		.o_tmr_dig_CLK_AUTO_TRIM_EN  (tmr_dig_clk_auto_trim_en_tck ));
	
	// internal
	assign	tmr_out_osc.pll_locked		= pll_locked;
	assign	tmr_out_osc.clkref_ok		= clkref_ok;
	
	// monitoring signals
	assign	tmr_out_osc.clkpll_div		= (tmr_out_osc.clock_selected == 1'b1) ? timebase_io.clkpll_div		: 1'b0;
	assign	tmr_out_osc.pll_down_mon	= (tmr_out_osc.clock_selected == 1'b1) ? timebase_io.pll_down_mon	: 1'b0;
	assign	tmr_out_osc.pll_up_mon		= (tmr_out_osc.clock_selected == 1'b1) ? timebase_io.pll_up_mon		: 1'b0;
	assign	tmr_out_osc.pll_lock_mon	= (tmr_out_osc.clock_selected == 1'b1) ? timebase_io.pll_lock_mon	: 1'b0;
	
	// clocks
	//FIXME: scan mux for clocks!
	always_comb begin
		if (tmr_out_osc.clock_selected == 1'b1) begin
			if (i_scanmode == 1'b1) tmr_out_osc.clkpll = pll_on;
			else 					tmr_out_osc.clkpll = timebase_io.clkpll;
		end
		else begin
			tmr_out_osc.clkpll = 1'b0;
		end
	end
	always_comb begin
		if (tmr_out_osc.clock_selected == 1'b1) begin
			if (i_scanmode == 1'b1) tmr_out_osc.clkosc = clk_ok;
			else 					tmr_out_osc.clkosc = clkosc_rst.clk;
		end
		else begin
			tmr_out_osc.clkosc = 1'b0;
		end
	end
	always_comb begin
		if (tmr_out_osc.clock_selected == 1'b1) begin
			if (i_scanmode == 1'b1) tmr_out_osc.clksys = pll_hold;
			else 					tmr_out_osc.clksys = clk_rst.clk;
		end
		else begin
			tmr_out_osc.clksys = 1'b0;
		end
	end
	
	// divided clocks
	clk_reset_if clkpll_rst ();
//	assign	clkpll_rst.clk = (i_scanmode == 1'b0) ? timebase_io.clkpll : clk_rst.clk;
	assign	clkpll_rst.clk = timebase_io.clkpll;
	assign	clkpll_rst.rstn = clk_rst.rstn;
	
	clk_div #(
			.factor       (18      )
		) i_clk_div_clkosc (
			.clk_rst      (clkosc_rst                ),
			.i_enable	  (tmr_out_osc.clock_selected),
			.clk_divided  (tmr_out_osc.clkosc_divided));
	
	clk_div #(
			.factor       (18      )
		) i_clk_div_clksys (
			.clk_rst      (clk_rst                   ),
			.i_enable	  (tmr_out_osc.clock_selected),
			.clk_divided  (tmr_out_osc.clksys_divided));
	
	clk_div #(
			.factor       (18      )
		) i_clk_div_clkpll (
			.clk_rst      (clkpll_rst.slave          ), 
			.i_enable	  (tmr_out_osc.clock_selected),			
			.clk_divided  (tmr_out_osc.clkpll_divided));
	
	// CLKREF
	assign	tmr_out_osc.clkref_filtered = (tmr_out_osc.clock_selected == 1'b1) ? timebase_io.clkref : 1'b0;
	assign	tmr_out_osc.clkref_divided = (tmr_out_osc.clock_selected == 1'b1) ? timebase_io.clkref_div : 1'b0;
	
	/*###   Auto trimming   ######################################################*/
	clock_auto_trimming i_clock_auto_trimming (
		.clk_rst                       (clk_rst                            ), 
		.time_base_registers_TRIM_OSC  (time_base_registers_TRIM_OSC.slave ), 
		.i_auto_trim_enable            (test_auto_trim_en                  ), 
		.i_clkref_rising               (clkref_rising                      ));
	
endmodule
