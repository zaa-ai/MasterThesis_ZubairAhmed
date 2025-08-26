//*********************************************************************
//
//Copyright (c) 2007 - 2014 Sidense Corp.
//
//This file contains confidential, proprietary information and trade
//secrets of Sidense. No part of this document may be used, reproduced
//or transmitted in any form or by any means without prior written
//permission of Sidense.
//
//Any trademarks are the property of their respective owner.
//
//Sidense Corp
//84 Hines Road, Suite 260
//Ottawa, ON
//Canada K2K 3G3
//
//email:  support@sidense.com
//
//*********************************************************************

`resetall
`timescale 1ns/1ps
`celldefine
`ifdef verifault
	`suppress_faults
	`enable_portfaults
`endif

module ips_tsmc180bcd50_p1r_ad(
		`ifdef HAVE_PG_PINS
			VDD,
			VSS,
			VCC,
		`endif
		CLKINSEL,
		CLKIN,
		VPPEN,
		MPP,
		VPPPAD,

		VRREN,
		MRR,

		CLKOUT,
		VPP,
		VBG,
		VREF,
		VRR,
		PPCLKOUT
		);

	`ifdef HAVE_PG_PINS
		inout VDD;
		inout VSS;
		inout VCC;
	`else
		supply1 VDD;
		supply0 VSS;
		supply1 VCC;
		assign VDD=1'b1;
		assign VSS=1'b0;
		assign VCC=1'b1;
	`endif

	input CLKINSEL;
	input CLKIN;
	input VPPEN;
	input [7:0] MPP;
	inout VPPPAD;

	input VRREN;
	input [15:0] MRR;

	output CLKOUT;
	inout VPP;
	inout VBG;
	inout VREF;
	inout VRR;
	output PPCLKOUT;

	wire powerOK;
	assign powerOK = (VDD === 1'b1) & (VCC === 1'b1) & (VSS === 1'b0) ;

	// MRR layout
	wire [3:0] VrrLevel;
	wire [2:0] VrefLevel;
	wire [1:0] VrrOutSel;
	wire VbgOutputEnable;
	wire VbgBiasDisable;
	wire VbgPowerDown;
	wire VrrPowerDown;
	wire VrefOutputEnable;
	wire VppOscillatorEnable;
	wire VppOscillatorReducedFrequency;

	assign VrrLevel = powerOK ? MRR[3:0] : 4'hx;
	assign VrefLevel = powerOK ? MRR[6:4] : 3'bxxx;
	assign VrrOutSel[0] = powerOK ? MRR[7] : 1'bx;
	assign VbgOutputEnable = powerOK ? MRR[8] : 1'bx;
	assign VbgBiasDisable = powerOK ? MRR[9] : 1'bx;
	assign VbgPowerDown = powerOK ? MRR[10] : 1'bx;
	assign VrrPowerDown = powerOK ? MRR[11] : 1'bx;
	assign VrefOutputEnable = powerOK ? MRR[12] : 1'bx;
	assign VppOscillatorEnable = powerOK ? MRR[13] : 1'bx;
	assign VppOscillatorReducedFrequency = powerOK ? MRR[14] : 1'bx;
	assign VrrOutSel[1] = powerOK ? MRR[15] : 1'bx;

	// MPP layout
	wire [1:0] VppLevel;
	wire VppLimitDis;
	wire VppReferenceSelector;
	wire [3:0] VppContolReserved;

	assign VppLevel = MPP[1:0];
	assign VppLimitDis = MPP[2];
	assign VppReferenceSelector = MPP[3];
	assign VppContolReserved = MPP[7:4];

	//Checks for Not Allowed and undefined controlls
	reg NA_vrr;
	reg NA_vref;
	reg NA_vbg;

	initial begin
		NA_vrr = 1'b0;
		NA_vref = 1'b0;
		NA_vbg = 1'b0;
	end

	always @(VRREN or MRR)
		casex ({VRREN,MRR[15],MRR[12:7]})
			8'b0_0_1xxxx1,
			8'b0_1_1xxxxx,
			8'b1_x_0110xx,
			8'b1_x_00x10x,
			8'b1_x_00100x,
			8'b1_x_00101x,
			8'b1_x_01000x,
			8'b1_x_01001x,
			8'b1_x_01x10x,
			8'b1_x_01x11x,
			8'b1_x_10x10x,
			8'b1_x_101xxx,
			8'b1_x_11xxxx: NA_vrr = 1'b1;
			default : NA_vrr = 1'b0;
		endcase

	always @(VRREN or MRR)
		casex ({VRREN,MRR[15],MRR[12:7]})
			8'b0_0_1xxxx1,
			8'b0_1_1xxxxx,
			8'b1_x_0110xx,
			8'b1_x_10x10x,
			8'b1_x_101xxx,
			8'b1_x_11xxxx: NA_vref = 1'b1;
			default : NA_vref = 1'b0;
		endcase

	always @(VRREN or MRR)
		casex ({VRREN,MRR[15],MRR[12:7]})
			8'b0_0_1xxxx1,
			8'b0_1_1xxxxx,
			8'b1_x_0110xx,
			8'b1_x_00101x,
			8'b1_x_10x10x,
			8'b1_x_101xxx,
			8'b1_x_11xxxx: NA_vbg = 1'b1;
			default : NA_vbg = 1'b0;
		endcase

	always @(NA_vrr)
		if (NA_vrr) begin
			force VRR = 1'bx;
			$display("\n<<SiDENSE_IPS_WARN [%0t]:%m: ",$realtime, "  %0s",  "Not Allowed controls for VRR applied. {VRREN,MRR[15],MRR[12:7]} = ", "%b_", VRREN, "%b_", MRR[15], "%b", MRR[12:7]);
		end else begin
			release VRR;
		end

	always @(NA_vref)
		if (NA_vref) begin
			force VREF = 1'bx;
			$display("\n<<SiDENSE_IPS_WARN [%0t]:%m: ",$realtime, "  %0s",  "Not Allowed controls for VREF applied. {VRREN,MRR[15],MRR[12:7]} = ", "%b_", VRREN, "%b_", MRR[15], "%b", MRR[12:7]);
		end else begin
			release VREF;
		end

	always @(NA_vbg)
		if (NA_vbg) begin
			force VBG = 1'bx;
			$display("\n<<SiDENSE_IPS_WARN [%0t]:%m: ",$realtime, "  %0s",  "Not Allowed controls for VBG applied. {VRREN,MRR[15],MRR[12:7]} = ", "%b_", VRREN, "%b_", MRR[15], "%b", MRR[12:7]);
		end else begin
			release VBG;
		end


		// VBG
	wire VbgOpAmpOut;
	wire VbgOpAmpEn;
	wire VbgPowerEn;
	wire VbgEna;
	wire VbgNode;

	assign VbgOpAmpEn  = VRREN & (~VbgBiasDisable);
	assign VbgPowerEn = VRREN & (~VbgPowerDown);
	assign VbgOpAmpOut = (VbgPowerEn === 1'b1) ? powerOK : 1'bx;
	assign VbgEna = VbgOutputEnable | VPPEN;

	bufif1  VBG_OpAmp(VbgNode, VbgOpAmpOut, VbgOpAmpEn);
	nmos    VBG_NMOS(VBG, VbgNode, VbgEna);

	// VRR
	wire VrrControlOK;
	wire VrrEna;
	reg VrrNode;
	reg VrrMuxOut;
	wire [1:0]VrrOutSel_gated;
	wire VrrPowerEn;

	assign VrrOutSel_gated = {2{~VRREN}} & VrrOutSel;
	assign VrrPowerEn = VRREN & (~VrrPowerDown);
	assign VrrControlOK = (^{VRREN, VrrLevel} !== 1'bx);
	assign VrrEna = ~((VRREN === 1'b0) & (VrrOutSel_gated === 2'b00));

	always @ (VRREN or VrrLevel or VrrPowerEn or VbgNode)
		if (^{VRREN, VrrLevel} === 1'bx) VrrNode = 1'bx;
		else if (VrrPowerEn === 1'b1) begin
			VrrNode = 1'bx;
			#(0.001) VrrNode = VbgNode;
		end else VrrNode = 1'bx;

	always @ (VrrOutSel_gated or VrrNode or VCC or VDD)
		case (VrrOutSel_gated)
			2'b00: VrrMuxOut = VrrNode;
			2'b01: VrrMuxOut = VCC;
			2'b10: VrrMuxOut = VCC;
			2'b11: VrrMuxOut = VDD;
			default : VrrMuxOut = 1'bx;
		endcase

	bufif1 VRR_BUF(VRR, VrrMuxOut, VrrEna);

	// VREF
	wire VrefControlOK;
	wire VrefEna;
	wire VrefNode;

	assign VrefControlOK = (^{VrefLevel} !== 1'bx);
	assign VrefEna = VrefOutputEnable;
	assign VrefNode = VrefControlOK ? VrrNode : 1'bx;

	nmos VREF_BUF(VREF, VrefNode, VrefEna);

	//VPP
	wire VppControlOK;
	wire VppEna;
	reg VppNode;

	assign VppControlOK = (^{VppReferenceSelector, VppLimitDis, VppLevel, VppOscillatorEnable, VppOscillatorReducedFrequency} !== 1'bx) & (VppContolReserved === 4'b0000);
	assign VppEna = (^VPPEN !== 1'bx) ? VPPEN : 1'bx;

	always @ (VppReferenceSelector or VppLimitDis or VppLevel or VppOscillatorEnable or VppOscillatorReducedFrequency or VppContolReserved or VDD or VBG)
		if ((^{VppReferenceSelector, VppLimitDis, VppLevel, VppOscillatorEnable, VppOscillatorReducedFrequency} === 1'bx) | (VppContolReserved !== 4'b0000))
			VppNode = 1'bx;
		else if (VppLimitDis == 1'b1) begin
			VppNode = 1'bx;
			#(0.001) VppNode = 1'b1;
		end else begin
			VppNode = 1'bx;
			#(0.001) VppNode = VppReferenceSelector ? VDD : VBG;
		end

	passthrough vpp_ext(VPP, VPPPAD);
	bufif1 VPP_BUF(VPP, VppNode, VppEna);


	// Pump Clock Generator
	parameter tpw_vpp_osc = 8.1; //62 Mhz
	parameter tpw_vpp_osc_delta = 2.5;
	parameter tpd_PPCLKOUT = 3.0;
	parameter tpd_CLKOUT = 2.0;
	parameter pump_en_osc = 100000.0; //100us

	reg vppClk;
	wire vppOscEna;

	assign vppOscEna = (VppOscillatorEnable | VPPEN) & (~CLKINSEL) ;

	initial begin
		#(pump_en_osc) vppClk = 1'b0;
		forever begin
			#(tpw_vpp_osc + (VppOscillatorReducedFrequency ? tpw_vpp_osc_delta : 0.0)) vppClk = vppOscEna;
			#(tpw_vpp_osc + (VppOscillatorReducedFrequency ? tpw_vpp_osc_delta : 0.0)) vppClk = vppOscEna ? 1'b0 : vppOscEna;
		end
	end

	assign #(tpd_CLKOUT) CLKOUT = (^CLKINSEL === 1'bx) ? 1'bx : (CLKINSEL == 1'b1) ? CLKIN : (vppOscEna ? vppClk : VDD);
	assign #(tpd_PPCLKOUT) PPCLKOUT = CLKOUT & VPPEN;


	specify

		specparam tVPP_WARMUP = 300.0:600.0:1600.0;
		specparam tVPP_SETUP  = 1000.0:1000.0:1000.0;
		specparam tVRR_WARMUP = 2900.0:3900.0:6800.0;
		specparam tVRR_SETUP  = 400.0:1700.0:4500.0;
		specparam tVBG_WARMUP = 1600.0:3000.0:5700.0;

		(VPPEN => VPP) = (tVPP_WARMUP, 0.0);
		(MPP[0] => VPP) = (tVPP_SETUP, 0.0);
		(MPP[1] => VPP) = (tVPP_SETUP, 0.0);
		(MPP[2] => VPP) = (tVPP_SETUP, 0.0);
		(MPP[3] => VPP) = (tVPP_SETUP, 0.0);

		(VRREN => VRR) = (tVRR_WARMUP, 0.0);
		(MRR[0] => VRR) = (tVRR_SETUP, 0.0);
		(MRR[1] => VRR) = (tVRR_SETUP, 0.0);
		(MRR[2] => VRR) = (tVRR_SETUP, 0.0);
		(MRR[3] => VRR) = (tVRR_SETUP, 0.0);

		(VRREN => VBG) = (tVBG_WARMUP, 0.0);

	endspecify

endmodule // ips_tsmc180bcd50_p1r_ad

`endcelldefine
`ifdef verifault
	`disable_portfaults
	`nosuppress_faults
`endif

module passthrough(.a(c), .b(c));
	inout c;
endmodule //passthrough
