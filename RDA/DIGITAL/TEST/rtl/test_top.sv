
/*==================================================
 *  Copyright (c) 2023 Elmos SE
 *  Author: stove
 *  Description : Note: This file has been generated automatically by stove
 *                Note: This file should not be modified manually.
 *                Standard test module for TEST_TOP in Test_Top
 *==================================================*/
module test_top #(
		parameter BASE_ADDR,
		parameter ADDR_WIDTH = 8
	)(
		jtag_bus_if.slave		jtag_bus,
		
		tmr_top_if.master  tmr_top,

		// TMR_SEL/_VAL
  

		output	logic[15:0]		o_jtag_dr
	);
	
	clk_reset_if clk_rst ();
	assign	clk_rst.clk = jtag_bus.clk;
	assign	clk_rst.rstn = jtag_bus.rstn;
	
	//==========================================================================
	// registers
	//==========================================================================
	`include "TEST_TOP_if_inst.sv"
	TEST_TOP #(
		.base_addr                   (BASE_ADDR                  ), 
		.addr_width                  (ADDR_WIDTH                 )
	) i_TEST_TOP (
		.clk_rst                     (clk_rst.slave              ), 
		.addr                        (jtag_bus.addr              ), 
		.data_in                     (jtag_bus.data_write        ), 
		.wr                          (jtag_bus.wr                ), 
		.rd                          (jtag_bus.rd                ),
		.TEST_TOP_TMR_ANA (TEST_TOP_TMR_ANA.master),
		.TEST_TOP_TMR_DIG (TEST_TOP_TMR_DIG.master),
		.TEST_TOP_TMR_IN (TEST_TOP_TMR_IN.master),
		.TEST_TOP_TMR_OUT_CSB_SCK (TEST_TOP_TMR_OUT_CSB_SCK.master),
		.TEST_TOP_TMR_OUT_MOSI_MISO (TEST_TOP_TMR_OUT_MOSI_MISO.master),
		.TEST_TOP_TMR_OUT_BFWB_SYNCB (TEST_TOP_TMR_OUT_BFWB_SYNCB.master),
		.TEST_TOP_TMR_OUT_DAB_INTB (TEST_TOP_TMR_OUT_DAB_INTB.master),
		.TEST_TOP_TMR_OUT_RFC (TEST_TOP_TMR_OUT_RFC.master),
		.data_out                    (o_jtag_dr                  ) 
	);
	
	//==========================================================================
	// TMR_ANA section
	//==========================================================================
	assign tmr_top.tmr_ana = TEST_TOP_TMR_ANA.value[0:0];
	
	//==========================================================================
	// TMR_DIG section
	//==========================================================================
	assign tmr_top.tmr_dig_use_jtag =TEST_TOP_TMR_DIG.USE_JTAG;
	assign tmr_top.tmr_dig_sel_sync =TEST_TOP_TMR_DIG.SEL_SYNC;
	assign tmr_top.tmr_dig_ignore_osc_ready =TEST_TOP_TMR_DIG.IGNORE_OSC_READY;
    
	//==========================================================================
	// TMR_OUT section
	//==========================================================================
	assign tmr_top.tmr_out_sel_sck = TEST_TOP_TMR_OUT_CSB_SCK.SEL_SCK;
	assign tmr_top.tmr_out_en_sck = TEST_TOP_TMR_OUT_CSB_SCK.EN_SCK;
	assign tmr_top.tmr_out_sel_csb = TEST_TOP_TMR_OUT_CSB_SCK.SEL_CSB;
	assign tmr_top.tmr_out_en_csb = TEST_TOP_TMR_OUT_CSB_SCK.EN_CSB;
	assign tmr_top.tmr_out_sel_miso = TEST_TOP_TMR_OUT_MOSI_MISO.SEL_MISO;
	assign tmr_top.tmr_out_en_miso = TEST_TOP_TMR_OUT_MOSI_MISO.EN_MISO;
	assign tmr_top.tmr_out_sel_mosi = TEST_TOP_TMR_OUT_MOSI_MISO.SEL_MOSI;
	assign tmr_top.tmr_out_en_mosi = TEST_TOP_TMR_OUT_MOSI_MISO.EN_MOSI;
	assign tmr_top.tmr_out_sel_syncb = TEST_TOP_TMR_OUT_BFWB_SYNCB.SEL_SYNCB;
	assign tmr_top.tmr_out_en_syncb = TEST_TOP_TMR_OUT_BFWB_SYNCB.EN_SYNCB;
	assign tmr_top.tmr_out_sel_bfwb = TEST_TOP_TMR_OUT_BFWB_SYNCB.SEL_BFWB;
	assign tmr_top.tmr_out_en_bfwb = TEST_TOP_TMR_OUT_BFWB_SYNCB.EN_BFWB;
	assign tmr_top.tmr_out_sel_intb = TEST_TOP_TMR_OUT_DAB_INTB.SEL_INTB;
	assign tmr_top.tmr_out_en_intb = TEST_TOP_TMR_OUT_DAB_INTB.EN_INTB;
	assign tmr_top.tmr_out_sel_dab = TEST_TOP_TMR_OUT_DAB_INTB.SEL_DAB;
	assign tmr_top.tmr_out_en_dab = TEST_TOP_TMR_OUT_DAB_INTB.EN_DAB;
	assign tmr_top.tmr_out_sel_rfc = TEST_TOP_TMR_OUT_RFC.SEL_RFC;
	assign tmr_top.tmr_out_en_rfc = TEST_TOP_TMR_OUT_RFC.EN_RFC;
  
	//==========================================================================
	// TMR_IN section
	//==========================================================================
	assign tmr_top.tmr_in[0] = TEST_TOP_TMR_IN.tmr_in_0;
	assign tmr_top.tmr_in[1] = TEST_TOP_TMR_IN.tmr_in_1;
	assign tmr_top.tmr_in[2] = TEST_TOP_TMR_IN.tmr_in_2;
	assign tmr_top.tmr_in[3] = TEST_TOP_TMR_IN.tmr_in_3;
  
 

endmodule
