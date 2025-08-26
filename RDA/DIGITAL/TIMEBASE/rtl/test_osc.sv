
/*==================================================
 *  Copyright (c) 2023 Elmos SE
 *  Author: stove
 *  Description : Note: This file has been generated automatically by stove
 *                Note: This file should not be modified manually.
 *                Standard test module for TEST_OSC in Test_oscillator_and_PLL
 *==================================================*/
module test_osc #(
		parameter BASE_ADDR,
		parameter ADDR_WIDTH = 8
	)(
		jtag_bus_if.slave		jtag_bus,
		
		tmr_osc_if.master  tmr_osc,

		// TMR_SEL/_VAL
		input	logic	i_PLL_ON_tmr_val, // signal from application for sel_val
		output	logic	o_PLL_ON_tmr_val, // signal muxed with tmr_val
		input	logic	i_PLL_HOLD_tmr_val, // signal from application for sel_val
		output	logic	o_PLL_HOLD_tmr_val, // signal muxed with tmr_val
  
		// TMR_DIG
		output  logic o_tmr_dig_CLKSW_TST_EN,
		output  logic o_tmr_dig_CLKSW_TST_SEL,
		output  logic o_tmr_dig_CLK_AUTO_TRIM_EN,

		output	logic[15:0]		o_jtag_dr
	);
	
	clk_reset_if clk_rst ();
	assign	clk_rst.clk = jtag_bus.clk;
	assign	clk_rst.rstn = jtag_bus.rstn;
	
	//==========================================================================
	// registers
	//==========================================================================
	`include "TEST_OSC_if_inst.sv"
	TEST_OSC #(
		.base_addr                   (BASE_ADDR                  ), 
		.addr_width                  (ADDR_WIDTH                 )
	) i_TEST_OSC (
		.clk_rst                     (clk_rst.slave              ), 
		.addr                        (jtag_bus.addr              ), 
		.data_in                     (jtag_bus.data_write        ), 
		.wr                          (jtag_bus.wr                ), 
		.rd                          (jtag_bus.rd                ),
		.TEST_OSC_TMR_ANA_TB_PLL (TEST_OSC_TMR_ANA_TB_PLL.master),
		.TEST_OSC_TMR_ANA_TB_OSC (TEST_OSC_TMR_ANA_TB_OSC.master),
		.TEST_OSC_TMR_DIG_TB (TEST_OSC_TMR_DIG_TB.master),
		.TEST_OSC_TMR_VAL_TB (TEST_OSC_TMR_VAL_TB.master),
		.TEST_OSC_TMR_SEL_TB (TEST_OSC_TMR_SEL_TB.master),
		.data_out                    (o_jtag_dr                  ) 
	);
	
	//==========================================================================
	// TMR_ANA section
	//==========================================================================
	assign tmr_osc.tmr_ana_tb_pll = TEST_OSC_TMR_ANA_TB_PLL.value[6:0];
	assign tmr_osc.tmr_ana_tb_osc = TEST_OSC_TMR_ANA_TB_OSC.value[2:0];
	
	//==========================================================================
	// TMR_DIG section
	//==========================================================================
	assign o_tmr_dig_CLKSW_TST_EN =TEST_OSC_TMR_DIG_TB.CLKSW_TST_EN;
	assign o_tmr_dig_CLKSW_TST_SEL =TEST_OSC_TMR_DIG_TB.CLKSW_TST_SEL;
	assign o_tmr_dig_CLK_AUTO_TRIM_EN =TEST_OSC_TMR_DIG_TB.CLK_AUTO_TRIM_EN;
    
	//==========================================================================
	// TMR_SEL/_VAL section
	//==========================================================================
	always_comb begin
		if (TEST_OSC_TMR_SEL_TB.PLL_ON == 1'b1)
			o_PLL_ON_tmr_val = TEST_OSC_TMR_VAL_TB.PLL_ON;
		else
			o_PLL_ON_tmr_val = i_PLL_ON_tmr_val;
	end
	always_comb begin
		if (TEST_OSC_TMR_SEL_TB.PLL_HOLD == 1'b1)
			o_PLL_HOLD_tmr_val = TEST_OSC_TMR_VAL_TB.PLL_HOLD;
		else
			o_PLL_HOLD_tmr_val = i_PLL_HOLD_tmr_val;
	end

endmodule
