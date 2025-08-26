`ifndef _TEST_ADDRESSES_PKG
`define _TEST_ADDRESSES_PKG
//==================================================
// Copyright (c) 2023 Elmos SE
// Author: stove
// Description : Note: This file has been generated automatically by stove
//               Note: This file should not be modified manually.
//               This file contains all test register addresses as constants and an associative array for test register naming
//==================================================
package test_addresses_pkg;
// @SuppressProblem -nowarnmiss 1 -type fully_unread_static_variable -count 100 -length 100
	const int ADDR_TEST_TOP_TMR_ANA = 'h1; /* Analog test register for switching internal signals to ATB.
'''Advice:''' Always write all Bits to 0 before switching to another signal. */
	const int ADDR_TEST_TOP_TMR_DIG = 'h2; /* Analog test register for switching internal signals to ATB.
Always write all Bits to 0 before switching to another signal. */
	const int ADDR_TEST_TOP_TMR_IN = 'h5; /* Set input signal from GPIO to certain digital signal */
	const int ADDR_TEST_TOP_TMR_OUT_CSB_SCK = 'h6; /* select output signal at CSB or SCK */
	const int ADDR_TEST_TOP_TMR_OUT_MOSI_MISO = 'h7; /* select output signal at MOSI or MISO */
	const int ADDR_TEST_TOP_TMR_OUT_BFWB_SYNCB = 'h8; /* select output signal at BFWB or SYNCB */
	const int ADDR_TEST_TOP_TMR_OUT_DAB_INTB = 'h9; /* select output signal at DAB or INTB */
	const int ADDR_TEST_TOP_TMR_OUT_RFC = 'ha; /* select output signal at RFC */
	const int ADDR_TEST_TOP_JTAG_ID = 'hfb; /* ID read out */
	const int ADDR_TEST_TOP_JTAG_BYPASS = 'hff; /* JTAG bypass
'''Note:''' data is shifted in and shifted out again */
	const int ADDR_TEST_SUP_TMR_ANA_SUPPLY = 'h10; /* analog test register for e.g. switchting internal signals to ATB.
'''Advice:''' Always write all Bits to 0 before switching to another signal. */
	const int ADDR_TEST_SUP_TMR_ANA_TEMP_SENSOR = 'h14; /* analog test register for e.g. switchting internal signals to ATB.
'''Advice:''' Always write all Bits to 0 before switching to another signal. */
	const int ADDR_TEST_SUP_TMR_ANA_OTP = 'h15; /* analog test register for e.g. switchting internal signals to ATB.
'''Advice:''' Always write all Bits to 0 before switching to another signal. */
	const int ADDR_TEST_SUP_TMR_DIG_SUPPLY = 'h11; /* digital test settings */
	const int ADDR_TEST_OSC_TMR_ANA_TB_PLL = 'h20; /* Analog test register for switching internal signals to ATB.
'''Advice:''' Always write all Bits to 0 before switching to another signal. */
	const int ADDR_TEST_OSC_TMR_ANA_TB_OSC = 'h21; /* Analog test register for switching internal signals to ATB.
'''Advice:''' Always write all Bits to 0 before switching to another signal. */
	const int ADDR_TEST_OSC_TMR_DIG_TB = 'h22; /* digital test settings */
	const int ADDR_TEST_OSC_TMR_VAL_TB = 'h23; /* Set value of digital signal when selected via TMR_SEL */
	const int ADDR_TEST_OSC_TMR_SEL_TB = 'h24; /* Selects digital signal for test input, value is set in Register TMR_VAL */
	const int ADDR_TEST_DSI_0_TMR_ANA_DSI3_TX = 'h30; /* Analog test register for switching internal signals to ATB.
'''Advice:''' Always write all Bits to 0 before switching to another signal. */
	const int ADDR_TEST_DSI_0_TMR_ANA_DSI3_RX = 'h31; /* Analog test register for switching internal signals to ATB.
'''Advice:''' Always write all Bits to 0 before switching to another signal. */
	const int ADDR_TEST_DSI_0_TMR_DIG_DSI3 = 'h32; /* digital test settings */
	const int ADDR_TEST_DSI_0_TMR_SEL_DSI3 = 'h33; /* Selects digital signal for test input, value is set in Register TMR_DIG_VAL */
	const int ADDR_TEST_DSI_0_TMR_VAL_DSI3 = 'h34; /* Set value of digital signal when selected via TMR_DIG_SEL */
	const int ADDR_TEST_DSI_0_TMR_IN_DSI3 = 'h35; /* Set input signal from GPIO to certain digital signal */
	const int ADDR_TEST_DSI_1_TMR_ANA_DSI3_TX = 'h40; /* Analog test register for switching internal signals to ATB.
'''Advice:''' Always write all Bits to 0 before switching to another signal. */
	const int ADDR_TEST_DSI_1_TMR_ANA_DSI3_RX = 'h41; /* Analog test register for switching internal signals to ATB.
'''Advice:''' Always write all Bits to 0 before switching to another signal. */
	const int ADDR_TEST_DSI_1_TMR_DIG_DSI3 = 'h42; /* digital test settings */
	const int ADDR_TEST_DSI_1_TMR_SEL_DSI3 = 'h43; /* Selects digital signal for test input, value is set in Register TMR_DIG_VAL */
	const int ADDR_TEST_DSI_1_TMR_VAL_DSI3 = 'h44; /* Set value of digital signal when selected via TMR_DIG_SEL */
	const int ADDR_TEST_DSI_1_TMR_IN_DSI3 = 'h45; /* Set input signal from GPIO to certain digital signal */
	const int ADDR_TEST_SCAN_SCAN = 'hb0; /* Enable ATPG scan test */
	const int ADDR_TEST_SRAM_SRAM_BIST_CTRL = 'hc8; /* control and configuration  SRAM BIST */
	const int ADDR_TEST_SRAM_SRAM_BIST_STAT = 'hc9; /* status of SRAM BIST */
	const int ADDR_TEST_SRAM_SRAM_ECC_CONTROL = 'hc7; /* Changing ECC values at certain points at SRAM */
	const int ADDR_TEST_OTP_CONFIG_OTP_WRITE_PULSE_WIDTH = 'haf; /* timing for OTP pulse width */
	const int ADDR_TEST_OTP_OTP_CONTROL = 'ha0; /* Test Access: OTP Control Register (16bit). Read only CPU access is implemented, all bits are hold in reset state if test is inactive. */
	const int ADDR_TEST_OTP_OTP_CONFIG = 'ha1; /* Test Access: OTP Config Register (32bit). No CPU access is implemented, all bits are hold in reset state if test is inactive. */
	const int ADDR_TEST_OTP_OTP_WRITE = 'ha2; /* write full Array */
	const int ADDR_TEST_OTP_OTP_READ = 'ha4; /* read full Array */
	const int ADDR_TEST_OTP_OTP_BIST_CONTROL = 'ha6; /* Test Access: OTP BIST Control Register (16bit). CPU Read/Write access. */
	const int ADDR_TEST_OTP_OTP_READ_CONFIG = 'ha7; /* Test Access: OTP Read Config (16bit). Read only CPU access is implemented, all bits are hold in reset state if test is inactive. */
	const int ADDR_TEST_OTP_OTP_BIST_STATUS = 'ha8; /* Test Access: OTP BIST Status (16bit) read only register. Read only CPU access is implemented. */
	const int ADDR_TEST_ELIP_IR_ELIP_RDF = 'hc0; /* ELIP read full (address + data)
'''Note:''' a dummy read has to be performed for proper read out */
	const int ADDR_TEST_ELIP_IR_ELIP_RD = 'hc1; /* ELIP read (again) - data output only */
	const int ADDR_TEST_ELIP_IR_ELIP_RDI = 'hc2; /* ELIP read and increment address - data output only */
	const int ADDR_TEST_ELIP_IR_ELIP_WRF = 'hc3; /* ELIP write full (address + data) */
	const int ADDR_TEST_ELIP_IR_ELIP_WR = 'hc4; /* ELIP write (again) - data input only */
	const int ADDR_TEST_ELIP_IR_ELIP_WRI = 'hc5; /* ELIP write and increment address - data input only */
	const int ADDR_TEST_WS_0_TMR_SEL_WS = 'h50; /*  */
	const int ADDR_TEST_WS_0_TMR_VAL_WS = 'h51; /*  */
	const int ADDR_TEST_WS_1_TMR_SEL_WS = 'h60; /*  */
	const int ADDR_TEST_WS_1_TMR_VAL_WS = 'h61; /*  */

	const string test_addresses[int]='{
		'h1 : "TEST_TOP_TMR_ANA",	
		'h2 : "TEST_TOP_TMR_DIG",	
		'h5 : "TEST_TOP_TMR_IN",	
		'h6 : "TEST_TOP_TMR_OUT_CSB_SCK",	
		'h7 : "TEST_TOP_TMR_OUT_MOSI_MISO",	
		'h8 : "TEST_TOP_TMR_OUT_BFWB_SYNCB",	
		'h9 : "TEST_TOP_TMR_OUT_DAB_INTB",	
		'ha : "TEST_TOP_TMR_OUT_RFC",	
		'hfb : "TEST_TOP_JTAG_ID",	
		'hff : "TEST_TOP_JTAG_BYPASS",	
		'h10 : "TEST_SUP_TMR_ANA_SUPPLY",	
		'h14 : "TEST_SUP_TMR_ANA_TEMP_SENSOR",	
		'h15 : "TEST_SUP_TMR_ANA_OTP",	
		'h11 : "TEST_SUP_TMR_DIG_SUPPLY",	
		'h20 : "TEST_OSC_TMR_ANA_TB_PLL",	
		'h21 : "TEST_OSC_TMR_ANA_TB_OSC",	
		'h22 : "TEST_OSC_TMR_DIG_TB",	
		'h23 : "TEST_OSC_TMR_VAL_TB",	
		'h24 : "TEST_OSC_TMR_SEL_TB",	
		'h30 : "TEST_DSI_0_TMR_ANA_DSI3_TX",	
		'h31 : "TEST_DSI_0_TMR_ANA_DSI3_RX",	
		'h32 : "TEST_DSI_0_TMR_DIG_DSI3",	
		'h33 : "TEST_DSI_0_TMR_SEL_DSI3",	
		'h34 : "TEST_DSI_0_TMR_VAL_DSI3",	
		'h35 : "TEST_DSI_0_TMR_IN_DSI3",	
		'h40 : "TEST_DSI_1_TMR_ANA_DSI3_TX",	
		'h41 : "TEST_DSI_1_TMR_ANA_DSI3_RX",	
		'h42 : "TEST_DSI_1_TMR_DIG_DSI3",	
		'h43 : "TEST_DSI_1_TMR_SEL_DSI3",	
		'h44 : "TEST_DSI_1_TMR_VAL_DSI3",	
		'h45 : "TEST_DSI_1_TMR_IN_DSI3",	
		'hb0 : "TEST_SCAN_SCAN",	
		'hc8 : "TEST_SRAM_SRAM_BIST_CTRL",	
		'hc9 : "TEST_SRAM_SRAM_BIST_STAT",	
		'hc7 : "TEST_SRAM_SRAM_ECC_CONTROL",	
		'haf : "TEST_OTP_CONFIG_OTP_WRITE_PULSE_WIDTH",	
		'ha0 : "TEST_OTP_OTP_CONTROL",	
		'ha1 : "TEST_OTP_OTP_CONFIG",	
		'ha2 : "TEST_OTP_OTP_WRITE",	
		'ha4 : "TEST_OTP_OTP_READ",	
		'ha6 : "TEST_OTP_OTP_BIST_CONTROL",	
		'ha7 : "TEST_OTP_OTP_READ_CONFIG",	
		'ha8 : "TEST_OTP_OTP_BIST_STATUS",	
		'hc0 : "TEST_ELIP_IR_ELIP_RDF",	
		'hc1 : "TEST_ELIP_IR_ELIP_RD",	
		'hc2 : "TEST_ELIP_IR_ELIP_RDI",	
		'hc3 : "TEST_ELIP_IR_ELIP_WRF",	
		'hc4 : "TEST_ELIP_IR_ELIP_WR",	
		'hc5 : "TEST_ELIP_IR_ELIP_WRI",	
		'h50 : "TEST_WS_0_TMR_SEL_WS",	
		'h51 : "TEST_WS_0_TMR_VAL_WS",	
		'h60 : "TEST_WS_1_TMR_SEL_WS",	
		'h61 : "TEST_WS_1_TMR_VAL_WS"	
	};

endpackage

`endif
	