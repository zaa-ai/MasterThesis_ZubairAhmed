module TOP #(
		parameter DSI3_COUNT = 4
	)(
		// SPI1
		inout	wire	MOSI_P,
		inout	wire	MISO_P,
		inout	wire	SCK_P,
		inout	wire	CSB_P,

		// SPI2 / JTAG
		inout	wire	INTB_P,
		inout	wire	RFC_P,
		inout	wire	DAB_P,
		inout	wire	BFWB_P,
		inout	wire	SYNCB_P,

		input 	wire	CLKREF_P,
		output 	real	AOUT_P,

		input	real	DGND_P,

		//DSI
		output	real	DSI_P[DSI3_COUNT-1:0],
		output	real	LDO_P,

		input	real	VSUP_P,
		input	real	GNDA_P,

		output	real	VCC_P,
		input	real	GNDD_P,

		output	real	VDD18_P,
		input	logic	TMODE_P,
		input	logic	RESB_P
		);

	logic[DSI3_COUNT*dsi3_pkg::DSI3_TX_DAC_WIDTH-1:0]	DSI3_TX_DATA;
	logic[DSI3_COUNT-1 : 0] DSI_OV;

	logic	PORB, VCC_OK, CLKREF_I;
	logic	LDO_OK;
	logic 	CLKREF_IE;

	logic VSS = 1'b0;

	`define def_pad_signal(_pad_) logic 	_pad_``_I_P, _pad_``_O_P, _pad_``_OE_P, _pad_``_PU_P, _pad_``_PD_P, _pad_``_IE_P;

	`def_pad_signal(CSB)
	`def_pad_signal(SCK)
	`def_pad_signal(SDI)
	`def_pad_signal(SDO)

	`def_pad_signal(RFC)
	`def_pad_signal(BFWB)
	`def_pad_signal(DAB)
	`def_pad_signal(INTB)
	`def_pad_signal(SYNCB)

	wire    SDO_P, SDI_P;

	wire	DS;

	always@(GNDD_P) begin
		if (GNDD_P != 0.0) begin
			$fatal("GNDD_P is not 0.0. GNDD_P=%f", GNDD_P);
		end
	end

	/*###   Assignments   ######################################################*/

	// bi directional pass switches
	tran (SDI_P, 	MOSI_P);
	tran (SDO_P, 	MISO_P);

	`define IO_PAD( _name_) IO_DIN_DIG #(.PullTime(10)) _name_``_PAD ( \
	.I       (_name_``_O_P      ), \
		.OE      (_name_``_OE_P     ), \
		.DS      (DS     	   ), \
		.PU      (_name_``_PU_P     ), \
		.PD      (_name_``_PD_P	   ), \
		.IE      (_name_``_IE_P	   ), \
		.C       (_name_``_I_P      ), \
		.AOUT    (		   	   ), \
		.PAD     (_name_``_P		  ));

	// pad cell instantiation
	`IO_PAD(CSB)
	`IO_PAD(SCK)
	`IO_PAD(SDI)
	`IO_PAD(SDO)
	`IO_PAD(RFC)
	`IO_PAD(BFWB)
	`IO_PAD(DAB)
	`IO_PAD(INTB)
	`IO_PAD(SYNCB)

	// padzelle für clkref
	IO_DIN_DIG #(.PullTime(10))	CLKREF_PAD (
			.AOUT    (   ),
			.C       (CLKREF_I  ),
			.DS      (DS     	),
			.I       (1'b0      	),
			.IE      (CLKREF_IE     	),
			.OE      (VSS    	),
			.PAD     (CLKREF_P	),
			.PD      (~PORB   	),
			.PU      (VSS    	));

	logic CLKOSC, OSC_ON, CLKPLL, CLKPLL_DIV, PLL_DOWN_MON, PLL_UP_MON, PLL_LOCK_MON;
	logic OTP_EHV_1V8, A_OTP_EHV, PLL_HOLD;
	logic[DSI3_COUNT-1:0]	DSI3_RXD1, DSI3_RXD2, DSI_UVB;
	logic	ON_PLL, OSC_READY;
	logic[DSI3_COUNT-1:0]	DSI_RX_TXN, DSI_RX_ON, DSI_TX_ON, DSI_TX_HVCASC_ON;
	logic[1:0]	TRIM_OT;
	logic[6:0]	TRIM_OSC_F;
	logic[2:0]	TRIM_OSC_TCF;
	logic[2:0]	ATST_OSC;
	logic[6:0]	ATST_PLL;
	logic	CLKREF_FILT;
	logic[DSI3_COUNT*2-1:0]DSI_TX_CFG;
	logic		LDO_EN, OT_ERROR, OT_WARN;
	
	logic	VDD_DISABLE;
	
	logic	A_OTP_VRR, VRR_OK;
    logic[DSI3_COUNT-1:0] DSI_ICMP;
    logic[DSI3_COUNT*5-1:0] DSI_IDAC;
    
	wire [DSI3_COUNT-1:0] DSI_RX_FILTER_FAST;
	ANA #(
			.DSI3_COUNT  (DSI3_COUNT )
		) XANA (
			.VSUP        (VSUP_P     ),
			.VCC         (VCC_P      ),
			.VDD18       (VDD18_P    ),
			.GND         (GNDA_P     ),
			.DGND        (DGND_P     ),

			.LDO		 (LDO_P),
			.LDO_CTRL	 ('0   ),
			.OT_ERROR	 (OT_ERROR),
			.OT_WARN	 (OT_WARN),
			.O_PORB      (PORB       ),
			.TRIM_OT     (TRIM_OT    ),
			.REG_VDD18_DIS (VDD_DISABLE),
			.VCC_OK    	 (VCC_OK     ),
			.A_OTP_VRR   (A_OTP_VRR  ),
			.VRR_OK      (VRR_OK     ),
			.LDO_OK      (LDO_OK     ),
			.LDO_EN	     (LDO_EN     ),

			.DSI3_REC1 (DSI3_RXD1),
			.DSI3_REC2 (DSI3_RXD2),
			.DSI3_TX   (DSI3_TX_DATA   ),
			.DSI_RX_TXN		(DSI_RX_TXN),
			.DSI_TX_CFG		(DSI_TX_CFG),
			.DSI_RX_ON		(DSI_RX_ON),
			.DSI_RX_FILTER_FAST(DSI_RX_FILTER_FAST),
			.DSI_TX_ON		(DSI_TX_ON),
			.DSI_TX_HVCASC_ON(DSI_TX_HVCASC_ON),
			.VDSI_CTRL   ('0   ),
            .DSI_RX_DAC    (DSI_IDAC    ),
            .DSI3_ILOAD_CMP(DSI_ICMP),

			.DSI		 (DSI_P),
			.DSI_UVB     (DSI_UVB	 ),
			.DSI_OV      (DSI_OV	 ),

			.AOUT		 (AOUT_P     ),
			.A_OTP_EHV	 (A_OTP_EHV  ),
            .OTP_EHV_1V8   (OTP_EHV_1V8   )
        );

	logic	CLKREF_DIV;
	osc_top XOSC (
			//			.AOUT           (),
			.ATST_PLL       (ATST_PLL      ),
			.CLKREF         (CLKREF_I      ),
			.CLKREF_FILT    (CLKREF_FILT   ),
			.CLKREF_DIV     (CLKREF_DIV    ),
			.RESB           (PORB          ),
			.ON_OSC         (OSC_ON        ),
			.ON_PLL         (ON_PLL        ),
			.PLL_HOLD       (PLL_HOLD      ),
			.OSC_F_TRIM     (TRIM_OSC_F    ),
			.OSC_TCF_TRIM   (TRIM_OSC_TCF  ),
			.ATST_OSC		(ATST_OSC[0]   ),
			.TST_OSC_SFMAX  (ATST_OSC[1]   ),
			.TST_OSC_SFMIN  (ATST_OSC[2]   ),
			.CLKOSC         (CLKOSC        ),
			.CLKPLL         (CLKPLL        ),
			.CLKPLL_DIV     (CLKPLL_DIV    ),
			.PLL_LOCK_MON   (PLL_LOCK_MON  ),
			.PLL_UP_MON     (PLL_UP_MON    ),
			.PLL_DOWN_MON   (PLL_DOWN_MON  ),
			.OSC_READY      (OSC_READY     ),
			.SUB            (GNDA_P        ),
			.VDD            (VDD18_P       ),
			.GND            (GNDA_P        ));

	logic	vcc_for_digital;
	assign	vcc_for_digital = (VCC_P > 4.5) ? 1'b1 : 1'b0;

	`define IO_PAD_CONNECT_( _name_ ) .I_``_name_ ( _name_``_I_P), \
	.O_``_name_ ( _name_``_O_P), \
	.O_``_name_``_OE ( _name_``_OE_P), \
	.O_``_name_``_IE ( _name_``_IE_P), \
	.O_``_name_``_PD ( _name_``_PD_P), \
	.O_``_name_``_PU ( _name_``_PU_P),


	digtop 
	`ifndef GATE_LEVEL #(
			.DSI3_COUNT  (DSI3_COUNT  )
		) `endif
	xdigtop (
			.VDD			(1'b1),
			.VSS			(1'b0),
			.VCC    		(vcc_for_digital    ),
			.PSUB           (1'b0),
			.VDD_NBL        (1'b1),
			.I_PORB      (PORB     	),
			.I_LDO_OK    (LDO_OK	),
			.I_VCC_OK	 (VCC_OK	),
			.I_VRR_OK      (VRR_OK),
			.O_TRIM_I5U		(),
			.O_LDO_EN		(LDO_EN),
			.I_OT_ERROR		(OT_ERROR),
			.I_OT_WARN		(OT_WARN),
			.O_TRIM_OT      (TRIM_OT),

			.I_CLKOSC    (CLKOSC   	),
			.O_OSC_ON	 (OSC_ON    ),
			.I_CLKPLL    (CLKPLL    ),
			.I_CLKPLL_DIV(CLKPLL_DIV),
			.I_PLL_LOCK_MON(PLL_LOCK_MON),
			.I_PLL_DOWN_MON(PLL_DOWN_MON),
			.I_PLL_UP_MON(PLL_UP_MON),
			.I_CLKREF    (CLKREF_FILT  ),
			.I_OSC_READY	(OSC_READY),
			.O_PLL_HOLD		(PLL_HOLD),
			.O_PLL_ON		(ON_PLL  ),
			.O_TRIM_OSC_F	(TRIM_OSC_F),
			.O_TRIM_OSC_TCF	(TRIM_OSC_TCF),
			.O_CLKREF_DIV  (CLKREF_DIV),

			.I_RESB      (RESB_P    ),

			// SPI
			`IO_PAD_CONNECT_(CSB)
			`IO_PAD_CONNECT_(SCK)
			`IO_PAD_CONNECT_(SDI)
			`IO_PAD_CONNECT_(SDO)
			`IO_PAD_CONNECT_(RFC)
			`IO_PAD_CONNECT_(BFWB)
			`IO_PAD_CONNECT_(DAB)
			`IO_PAD_CONNECT_(INTB)
			`IO_PAD_CONNECT_(SYNCB)

			//
			.I_TMODE    (TMODE_P    ),
			.O_CLKREF_IE(CLKREF_IE		 ),
			.O_PAD_DS   (DS         ),

			.I_DSI_RXD1  (DSI3_RXD1  ),
			.I_DSI_RXD2  (DSI3_RXD2  ),
			.O_DSI_TX_DATA  (DSI3_TX_DATA  ),
			.O_DSI_RX_TXN (DSI_RX_TXN),
			.O_DSI_TX_TBIT_CFG (DSI_TX_CFG),
			.I_DSI_UVB		(DSI_UVB	),
			.I_DSI_OV		(DSI_OV	),
			.O_DSI_TX_ON	(DSI_TX_ON),
			.O_DSI_TX_HVCASC_ON(DSI_TX_HVCASC_ON),
			.O_DSI_RX_ON	(DSI_RX_ON),
            .I_DSI_ICMP     (DSI_ICMP),
            .O_DSI_IDAC     (DSI_IDAC),
			.O_TRIM_DSI_RX1	(),
			.O_TRIM_DSI_RX2	(),

			.O_OTP_EHV		(OTP_EHV_1V8),
			.A_OTP_EHV    (A_OTP_EHV),
			//.A_OTP_VBG    (		    ), //ToDo: connect to ATB
			.A_OTP_VPP    (     	), //ToDo: connect to ATB
			.A_OTP_VREF   (         ), //ToDo: connect to ATB
			.A_OTP_VRR    (A_OTP_VRR), //ToDo: connect to ATB
			.O_AOUT_ENABLE(			),

			.O_ATST_OSC        (ATST_OSC),
			.O_ATST_OTP        (		),
			.O_ATST_PLL        (ATST_PLL),
			.O_ATST_RX         (		),
			.O_ATST_SUP        (        ),
			.O_ATST_TX         (		),
			.O_ATST_TEMP_SENSOR(),
			.O_VDD_VOLTAGE_DIVIDER_DISABLE (),
			.O_VDD_LOAD_DISABLE(),
			.O_VDD_DISABLE (VDD_DISABLE),
            .O_DSI_RX_FILTER_FAST(DSI_RX_FILTER_FAST)
        );

endmodule
