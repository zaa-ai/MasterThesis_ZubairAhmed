//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------

module top_th;

	timeunit      1ns;
	timeprecision 1ps;

	import common_pkg::*;
	import common_env_pkg::*;
	
	// Pin-level interfaces connected to DUT
	// You can remove interface instances by setting generate_interface_instance = no in the interface template file
	
	jtag_master_if jtag_master();
	spi_if spi();
	dsi3_slave_if dsi3_slave[1:0]();		
	digital_signal_if tmode();
	digital_signal_if resb();
	digital_signal_if rfc();
	digital_signal_if bfwb();
	digital_signal_if dab();
	digital_signal_if intb();
	digital_signal_if syncb();
	digital_signal_if syncb_out();
	osc_if osc();
	real_signal_if iload[1:0]();		
	real_signal_if vsup();
	real_signal_if vcc();
	real_signal_if vdd18();
	real_signal_if aout();
	real_signal_if ldo();
	real_signal_if temp();
	
	// You can insert code here by setting th_inc_inside_module in file common.tpl
	
	TOP_WRAPPER i_dut_wrapper (
		.TCK_P (jtag_master.TCK),
		.TDI_P (jtag_master.TDI),
		.TDO_P (jtag_master.TDO),
		.TMS_P (jtag_master.TMS),
		.CSB_P (spi.CSN),
		.SCK_P (spi.SCK),
		.MOSI_P (spi.SDI),
		.MISO_P (spi.SDO),
		.TMODE_P (tmode.D),
		.RESB_P (resb.D),
		.RFC_P (rfc.D),
		.BFWB_P (bfwb.D),
		.DAB_P (dab.D),
		.INTB_P (intb.D),
		.SYNCB_P (syncb.D),
		.SYNCB_OUT_P (syncb_out.D),
		.CLKREF_P (osc.CLK),
		.CLKREF_EN_P (osc.EN),
		.ILOAD (iload),
		.VSUP_P (vsup.PIN),
		.VCC_P (vcc.PIN),
		.VDD18_P (vdd18.PIN),
		.AOUT_P (aout.PIN),
		.LDO_P (ldo.PIN),
		.TEMP (temp.PIN),
		.DSI_P (dsi3_slave)
	);
	
endmodule