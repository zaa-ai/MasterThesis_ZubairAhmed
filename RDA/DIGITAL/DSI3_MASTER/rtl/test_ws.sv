
/*==================================================
 *  Copyright (c) 2023 Elmos SE
 *  Author: stove
 *  Description : Note: This file has been generated automatically by stove
 *                Note: This file should not be modified manually.
 *                Standard test module for TEST_WS in Test_WS
 *==================================================*/
module test_ws #(
		parameter BASE_ADDR,
		parameter ADDR_WIDTH = 8
	)(
		jtag_bus_if.slave		jtag_bus,
		

		// TMR_SEL/_VAL
		input	logic [4:0]	i_DAC_tmr_val, // signal from application for sel_val
		output	logic [4:0]	o_DAC_tmr_val, // signal muxed with tmr_val
  
		// TMR_DIG

		output	logic[15:0]		o_jtag_dr
	);
	
	clk_reset_if clk_rst ();
	assign	clk_rst.clk = jtag_bus.clk;
	assign	clk_rst.rstn = jtag_bus.rstn;
	
	//==========================================================================
	// registers
	//==========================================================================
	`include "TEST_WS_if_inst.sv"
	TEST_WS #(
		.base_addr                   (BASE_ADDR                  ), 
		.addr_width                  (ADDR_WIDTH                 )
	) i_TEST_WS (
		.clk_rst                     (clk_rst.slave              ), 
		.addr                        (jtag_bus.addr              ), 
		.data_in                     (jtag_bus.data_write        ), 
		.wr                          (jtag_bus.wr                ), 
		.rd                          (jtag_bus.rd                ),
		.TEST_WS_TMR_SEL_WS (TEST_WS_TMR_SEL_WS.master),
		.TEST_WS_TMR_VAL_WS (TEST_WS_TMR_VAL_WS.master),
		.data_out                    (o_jtag_dr                  ) 
	);
	
	//==========================================================================
	// TMR_SEL/_VAL section
	//==========================================================================
	always_comb begin
		if (TEST_WS_TMR_SEL_WS.DAC == 1'b1)
			o_DAC_tmr_val = TEST_WS_TMR_VAL_WS.DAC;
		else
			o_DAC_tmr_val = i_DAC_tmr_val;
	end

endmodule
