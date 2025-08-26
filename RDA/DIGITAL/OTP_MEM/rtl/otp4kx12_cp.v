//-----------------------------------------------------------------------------
// Title       : OTP4KX12_CP
// Project     : Standard
//-----------------------------------------------------------------------------
// Description : Charge-Pump and OTP as one analog block
//-----------------------------------------------------------------------------
// Subblocks   : ips_tsmc180bcd50_p1r_ad slp_b_tsmc180bcd50_4kx12_cm16d_ab
//-----------------------------------------------------------------------------
// File        : otp4kx12_cp.v
// Author      : Denis Poliakov (DPOL) ELSPB
// Company     : ELMOS Semiconductor AG
// Created     : 17.04.2017
// Last update : 06.06.2017
//-----------------------------------------------------------------------------
// Copyright (c) 2017 ELMOS Semiconductor AG
//-----------------------------------------------------------------------------
// Revisions   :
// Date        Version  Author  Description
// 17.04.2017   1.0     dpol    initial release
// 06.06.2017   1.1     dpol    interface names corrected
//-----------------------------------------------------------------------------

`timescale 1ns/1ps

module otp4kx12_cp (
		// Charge-Pump Control
		VPPEN,
		VRREN,
		MPP,
		MRR,
		CLKOUT,
		PPCLKOUT,
		// OTP Array Control
		OE,
		SEL,
		WE,
		CK,
		MR,
		ADDR,
		DW,
		DR,
		// Analog signals
		EHV,
		VBG,
		VPPPAD,
		VREF,
		VRR
		);

	parameter dataWidth = 12;
	parameter addressWidth = 12;
	parameter modeWidth = 8;

	`ifdef HAVE_PG_PINS
		// Power
		supply0 VSS;
		supply1 VDD;
		supply1 VCC;
	`endif


	// Digital Interface to Charge-Pump
	input VPPEN;
	input VRREN;
	input  [7:0] MPP;
	input [15:0] MRR;
	output CLKOUT;
	output PPCLKOUT;

	// Array OTP 12bit
	input OE;
	input SEL;
	input WE;
	input CK;
	input [(modeWidth-1):0] MR;
	input [(addressWidth-1):0] ADDR;
	input  [(dataWidth-1):0] DW;
	output [(dataWidth-1):0] DR;

	// Analog Interface to Charge-Pump
	input EHV;
	output VBG;
	output VPPPAD;
	output VREF;
	output VRR;

	// internal interface between Charge-Pump and OTP Arrays
	//wire VPP;


	//-----------------------------------------------------------------------------
	// subblocks instantiations
	//-----------------------------------------------------------------------------
	ips_tsmc180bcd50_p1r_ad u_ips (
			`ifdef HAVE_PG_PINS
				.VDD      (VDD),
				.VSS      (VSS),
				.VCC      (VCC),
			`endif
			.CLKINSEL (1'b0),
			.CLKIN    (1'b0),
			.VPPEN    (VPPEN),
			.MPP      (MPP),
			// @SuppressProblem -type explicit_unconnected_instance_input -count 1 -length 1
			.VPPPAD   (),
			.VRREN    (VRREN),
			.MRR      (MRR),
			.CLKOUT   (CLKOUT),
			.VPP      (VPPPAD),
			.VBG      (VBG),
			.VREF     (VREF),
			.VRR      (VRR),
			.PPCLKOUT (PPCLKOUT)
		);
	//-----------------------------------------------------------------------------
	slp_b_tsmc180bcd50_4kx12_cm16d_ab_r20 u_otp4kx12 (
			.SEL  (SEL),
			.CK   (CK),
			.A    (ADDR),
			.WE   (WE),
			.D    (DW),
			.Q    (DR),
			.OE   (OE),
			.MR   (MR),
			.VREF (VREF),
			.EHV  (EHV),
			.VPP  (VPPPAD),
			.VRR  (VRR)
		);
	//-----------------------------------------------------------------------------
endmodule
