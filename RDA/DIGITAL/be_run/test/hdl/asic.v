`timescale 1ns / 10ps	

module asic (
		input  TMODE,
		input  PORB,
		input  RESB, // scan_reset
		input  RFC, // scan enable
		input  SDI, // scan data in 1
		output SDO, // scan data out 1
		input  DAB, // scan data in 2
		output INTB, //scan data out 2
		input  CSB, // scan data in 3
		inout  SYNCB, // scan data out3 / TDI open drain with pull up? 
		input  BFWB, // TCK
		input  SCK
		);
	
	//==========================================================================
	// DSI Inputs
	//==========================================================================
	wire[1:0]	DSI3_RXD1, DSI3_RXD2, DSI_UVB, DSI_OV;

	assign DSI3_RXD1 = 2'bx;
	assign DSI3_RXD2 = 2'bx;
	assign DSI_UVB   = 2'bx;
	assign DSI_OV    = 2'bx;
		
	
	//==========================================================================
	// GPIO pads
	//==========================================================================
	wire RFC_I_P, SDI_I_P, DAB_I_P, CSB_I_P, BFWB_I_P, SCK_I_P, SDO_I_P, INTB_I_P;
	
	assign RFC_I_P = RFC;
	assign SDI_I_P = SDI;
	assign DAB_I_P = DAB;
	assign CSB_I_P = CSB;
	assign BFWB_I_P = BFWB;
	assign SCK_I_P  = SCK;
	
	assign SDO_I_P = 1'bx;
	assign INTB_I_P = 1'bx;
	
	wire SDO_O_P, INTB_O_P;
	
	assign SDO = SDO_O_P;
	assign INTB = INTB_O_P;
	
	wire SYNCB_OE_P, SYNCB_O_P, SYNCB_I_P, SYNCB_IE_P;
	
	// Bidirectional Pin Syncb Input: TDI for test setup, Output: ScanOut 3
	assign SYNCB = SYNCB_OE_P ? SYNCB_O_P : 1'bz;
	assign SYNCB_I_P = SYNCB_IE_P ? SYNCB : 1'b0;

	//==========================================================================
	// digital instance
	//==========================================================================	 

	digtop xdigtop (
			.I_PORB         (PORB),
			.I_LDO_OK       (1'bx),
			.I_VCC_OK	    (1'bx),
			.I_VRR_OK       (1'bx),
			.O_TRIM_I5U		(),
			.O_LDO_EN		(),
			.I_OT_ERROR		(1'bx),
			.I_OT_WARN		(1'bx),
			.O_TRIM_OT      (),

			.I_CLKOSC       (1'b0),
			.O_OSC_ON	    (),
			.I_CLKPLL       (1'b0),
			.I_CLKPLL_DIV   (1'bx),
			.I_PLL_LOCK_MON (1'bx),
			.I_PLL_DOWN_MON (1'bx),
			.I_PLL_UP_MON   (1'bx),
			.I_CLKREF       (1'bx),
			.I_OSC_READY	(1'bx),
			.O_PLL_HOLD		(),
			.O_PLL_ON		(),
			.O_TRIM_OSC_F	(),
			.O_TRIM_OSC_TCF	(),
			.O_CLKREF_DIV   (),

			.I_RESB         (RESB),

			// SPI
			.I_CSB    ( CSB_I_P), 
			.O_CSB    ( ), 
			.O_CSB_OE ( ), 
			.O_CSB_IE ( ), 
			.O_CSB_PD ( ),
			.O_CSB_PU ( ),

			.I_SCK ( SCK_I_P), 
			.O_SCK      ( ), 
			.O_SCK_OE ( ), 
			.O_SCK_IE ( ), 
			.O_SCK_PD ( ),
			.O_SCK_PU ( ),

			.I_SDI ( SDI_I_P), 
			.O_SDI      ( ), 
			.O_SDI_OE ( ), 
			.O_SDI_IE ( ), 
			.O_SDI_PD ( ),
			.O_SDI_PU ( ),

			.I_SDO ( SDO_I_P), 
			.O_SDO      ( SDO_O_P), 
			.O_SDO_OE ( SDO_OE_P), 
			.O_SDO_IE ( SDO_IE_P), 
			.O_SDO_PD ( SDO_PD_P),
			.O_SDO_PU ( SDO_PU_P),

			.I_RFC ( RFC_I_P), 
			.O_RFC      ( RFC_O_P), 
			.O_RFC_OE ( RFC_OE_P), 
			.O_RFC_IE ( RFC_IE_P), 
			.O_RFC_PD ( RFC_PD_P),
			.O_RFC_PU ( RFC_PU_P),

			.I_BFWB ( BFWB_I_P), 
			.O_BFWB    ( BFWB_O_P), 
			.O_BFWB_OE ( BFWB_OE_P), 
			.O_BFWB_IE ( BFWB_IE_P), 
			.O_BFWB_PD ( BFWB_PD_P),
			.O_BFWB_PU ( BFWB_PU_P),

			.I_DAB ( DAB_I_P), 
			.O_DAB      ( DAB_O_P), 
			.O_DAB_OE ( DAB_OE_P), 
			.O_DAB_IE ( DAB_IE_P), 
			.O_DAB_PD ( DAB_PD_P),
			.O_DAB_PU ( DAB_PU_P),

			.I_INTB ( INTB_I_P), 
			.O_INTB      ( INTB_O_P), 
			.O_INTB_OE ( ), 
			.O_INTB_IE ( ), 
			.O_INTB_PD ( ),
			.O_INTB_PU ( ),

			.I_SYNCB ( SYNCB_I_P ), 
			.O_SYNCB      ( SYNCB_O_P), 
			.O_SYNCB_OE ( SYNCB_OE_P), 
			.O_SYNCB_IE ( SYNCB_IE_P), 
			.O_SYNCB_PD ( SYNCB_PD_P),
			.O_SYNCB_PU ( SYNCB_PU_P),

			//
			.I_TMODE        (TMODE),
			.O_CLKREF_IE    (),
			.O_PAD_DS       (),

			.I_DSI_RXD1     (DSI3_RXD1  ),
			.I_DSI_RXD2     (DSI3_RXD2  ),
			.O_DSI_TX_DATA  (),
			.O_DSI_RX_TXN   (),
			.O_DSI_TX_TBIT_CFG (),
			.I_DSI_UVB		(DSI_UVB	),
			.I_DSI_OV		(DSI_OV	),
			.O_DSI_TX_ON	(),
			.O_DSI_TX_HVCASC_ON (),
			.O_DSI_RX_ON	(),
			.O_DSI_IDAC     (),
			.I_DSI_ICMP     (2'bx),
			.O_TRIM_DSI_RX1	(),
			.O_TRIM_DSI_RX2	(),

			.O_OTP_EHV		(),
			.A_OTP_EHV      (1'b0),
			.A_OTP_VPP      (), 
			.A_OTP_VREF     (), 
			.A_OTP_VRR      (), 
			.O_AOUT_ENABLE  (),

			.O_ATST_OSC         (),
			.O_ATST_OTP         (),
			.O_ATST_PLL         (),
			.O_ATST_RX          (),
			.O_ATST_SUP         (),
			.O_ATST_TX          (),
			.O_ATST_TEMP_SENSOR (),
			.O_VDD_VOLTAGE_DIVIDER_DISABLE (),
			.O_VDD_LOAD_DISABLE (),
			.O_VDD_DISABLE (),
			.O_DSI_RX_FILTER_FAST()
		);
 
endmodule

