
/*==================================================
 *  Copyright (c) 2023 Elmos SE
 *  Author: stove
 *  Description : Note: This file has been generated automatically by stove
 *                Note: This file should not be modified manually.
 *                Standard test module for TEST_SUPPLY in Test_Supply
 *==================================================*/
module test_supply #(
		parameter BASE_ADDR,
		parameter ADDR_WIDTH = 8
	)(
		jtag_bus_if.slave		jtag_bus,
		
		tmr_supply_if.master  tmr_supply,

		// TMR_SEL/_VAL
  
		// TMR_DIG
		output  logic o_tmr_dig_PREVENT_OVERTEMPERATURE_SWITCH_OFF,

		output	logic[15:0]		o_jtag_dr
	);
	
	clk_reset_if clk_rst ();
	assign	clk_rst.clk = jtag_bus.clk;
	assign	clk_rst.rstn = jtag_bus.rstn;
	
	//==========================================================================
	// registers
	//==========================================================================
	`include "TEST_SUPPLY_if_inst.sv"
	TEST_SUPPLY #(
		.base_addr                   (BASE_ADDR                  ), 
		.addr_width                  (ADDR_WIDTH                 )
	) i_TEST_SUPPLY (
		.clk_rst                     (clk_rst.slave              ), 
		.addr                        (jtag_bus.addr              ), 
		.data_in                     (jtag_bus.data_write        ), 
		.wr                          (jtag_bus.wr                ), 
		.rd                          (jtag_bus.rd                ),
		.TEST_SUPPLY_TMR_ANA_SUPPLY (TEST_SUPPLY_TMR_ANA_SUPPLY.master),
		.TEST_SUPPLY_TMR_ANA_TEMP_SENSOR (TEST_SUPPLY_TMR_ANA_TEMP_SENSOR.master),
		.TEST_SUPPLY_TMR_ANA_OTP (TEST_SUPPLY_TMR_ANA_OTP.master),
		.TEST_SUPPLY_TMR_DIG_SUPPLY (TEST_SUPPLY_TMR_DIG_SUPPLY.master),
		.data_out                    (o_jtag_dr                  ) 
	);
	
	//==========================================================================
	// TMR_ANA section
	//==========================================================================
	assign tmr_supply.tmr_ana_supply = TEST_SUPPLY_TMR_ANA_SUPPLY.value[4:0];
	assign tmr_supply.tmr_ana_temp_sensor = TEST_SUPPLY_TMR_ANA_TEMP_SENSOR.value[1:0];
	assign tmr_supply.tmr_ana_otp = TEST_SUPPLY_TMR_ANA_OTP.value[5:0];
	
	//==========================================================================
	// TMR_DIG section
	//==========================================================================
	assign o_tmr_dig_PREVENT_OVERTEMPERATURE_SWITCH_OFF =TEST_SUPPLY_TMR_DIG_SUPPLY.PREVENT_OVERTEMPERATURE_SWITCH_OFF;
    
 

endmodule
