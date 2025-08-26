
/*==================================================
 *  Copyright (c) 2023 Elmos SE
 *  Author: stove
 *  Description : Note: This file has been generated automatically by stove
 *                Note: This file should not be modified manually.
 *                Standard test module for TEST_DSI in Test_DSI3
 *==================================================*/
module test_dsi #(
		parameter BASE_ADDR,
		parameter ADDR_WIDTH = 8
	)(
		jtag_bus_if.slave		jtag_bus,
		
		tmr_dsi_if.master  tmr_dsi,

  		// TMR_IN
		input	logic	i_tx_tmr_in,  // signal from application
		output	logic	o_tx_tmr_in,  // signal muxed with tmr_in

		// TMR_SEL/_VAL
		input	logic	i_TX_tmr_val, // signal from application for sel_val
		output	logic	o_TX_tmr_val, // signal muxed with tmr_val
		input	logic	i_RX_TXN_tmr_val, // signal from application for sel_val
		output	logic	o_RX_TXN_tmr_val, // signal muxed with tmr_val
		input	logic	i_TX_ON_tmr_val, // signal from application for sel_val
		output	logic	o_TX_ON_tmr_val, // signal muxed with tmr_val
		input	logic	i_HVCASC_ON_tmr_val, // signal from application for sel_val
		output	logic	o_HVCASC_ON_tmr_val, // signal muxed with tmr_val
		input	logic	i_RX_ON_tmr_val, // signal from application for sel_val
		output	logic	o_RX_ON_tmr_val, // signal muxed with tmr_val
  
		// TMR_DIG
		output  logic o_tmr_dig_PREVENT_DEACTIVATION,

		output	logic[15:0]		o_jtag_dr
	);
	
	clk_reset_if clk_rst ();
	assign	clk_rst.clk = jtag_bus.clk;
	assign	clk_rst.rstn = jtag_bus.rstn;
	
	//==========================================================================
	// registers
	//==========================================================================
	`include "TEST_DSI_if_inst.sv"
	TEST_DSI #(
		.base_addr                   (BASE_ADDR                  ), 
		.addr_width                  (ADDR_WIDTH                 )
	) i_TEST_DSI (
		.clk_rst                     (clk_rst.slave              ), 
		.addr                        (jtag_bus.addr              ), 
		.data_in                     (jtag_bus.data_write        ), 
		.wr                          (jtag_bus.wr                ), 
		.rd                          (jtag_bus.rd                ),
		.TEST_DSI_TMR_ANA_DSI3_TX (TEST_DSI_TMR_ANA_DSI3_TX.master),
		.TEST_DSI_TMR_ANA_DSI3_RX (TEST_DSI_TMR_ANA_DSI3_RX.master),
		.TEST_DSI_TMR_DIG_DSI3 (TEST_DSI_TMR_DIG_DSI3.master),
		.TEST_DSI_TMR_SEL_DSI3 (TEST_DSI_TMR_SEL_DSI3.master),
		.TEST_DSI_TMR_VAL_DSI3 (TEST_DSI_TMR_VAL_DSI3.master),
		.TEST_DSI_TMR_IN_DSI3 (TEST_DSI_TMR_IN_DSI3.master),
		.data_out                    (o_jtag_dr                  ) 
	);
	
	//==========================================================================
	// TMR_ANA section
	//==========================================================================
	assign tmr_dsi.tmr_ana_dsi3_tx = TEST_DSI_TMR_ANA_DSI3_TX.value[6:0];
	assign tmr_dsi.tmr_ana_dsi3_rx = TEST_DSI_TMR_ANA_DSI3_RX.value[0:0];
	
	//==========================================================================
	// TMR_DIG section
	//==========================================================================
	assign o_tmr_dig_PREVENT_DEACTIVATION =TEST_DSI_TMR_DIG_DSI3.PREVENT_DEACTIVATION;
    
	//==========================================================================
	// TMR_IN section
	//==========================================================================
	always_comb begin
    	if (TEST_DSI_TMR_IN_DSI3.tmr_in_tx == '0) begin
			o_tx_tmr_in = i_tx_tmr_in;
		end
		else begin
			if (TEST_DSI_TMR_IN_DSI3.tmr_in_tx < 3'd5) begin
				o_tx_tmr_in = tmr_dsi.tmr_in[TEST_DSI_TMR_IN_DSI3.tmr_in_tx-1];
			end
			else begin
				o_tx_tmr_in = i_tx_tmr_in;
			end
		end
    end
  
	//==========================================================================
	// TMR_SEL/_VAL section
	//==========================================================================
	always_comb begin
		if (TEST_DSI_TMR_SEL_DSI3.TX == 1'b1)
			o_TX_tmr_val = TEST_DSI_TMR_VAL_DSI3.TX;
		else
			o_TX_tmr_val = i_TX_tmr_val;
	end
	always_comb begin
		if (TEST_DSI_TMR_SEL_DSI3.RX_TXN == 1'b1)
			o_RX_TXN_tmr_val = TEST_DSI_TMR_VAL_DSI3.RX_TXN;
		else
			o_RX_TXN_tmr_val = i_RX_TXN_tmr_val;
	end
	always_comb begin
		if (TEST_DSI_TMR_SEL_DSI3.TX_ON == 1'b1)
			o_TX_ON_tmr_val = TEST_DSI_TMR_VAL_DSI3.TX_ON;
		else
			o_TX_ON_tmr_val = i_TX_ON_tmr_val;
	end
	always_comb begin
		if (TEST_DSI_TMR_SEL_DSI3.HVCASC_ON == 1'b1)
			o_HVCASC_ON_tmr_val = TEST_DSI_TMR_VAL_DSI3.HVCASC_ON;
		else
			o_HVCASC_ON_tmr_val = i_HVCASC_ON_tmr_val;
	end
	always_comb begin
		if (TEST_DSI_TMR_SEL_DSI3.RX_ON == 1'b1)
			o_RX_ON_tmr_val = TEST_DSI_TMR_VAL_DSI3.RX_ON;
		else
			o_RX_ON_tmr_val = i_RX_ON_tmr_val;
	end

endmodule
