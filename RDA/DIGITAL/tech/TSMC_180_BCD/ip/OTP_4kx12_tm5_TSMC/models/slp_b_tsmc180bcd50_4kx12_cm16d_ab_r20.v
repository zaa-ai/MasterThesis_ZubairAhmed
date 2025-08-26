//****************************************************************************
//
//  Copyright (c) 2007 - 2017 Sidense Corp.
//
//  This file contains confidential, proprietary information and trade
//  secrets of Sidense. No part of this document may be used, reproduced
//  or transmitted in any form or by any means without prior written
//  permission of Sidense.
//
//  Any trademarks are the property of their respective owner.
//
//  Sidense Corp
//  84 Hines Road, Suite 260
//  Ottawa, ON
//  Canada K2K 3G3
//
//  email:  support@sidense.com
//
//****************************************************************************

//****************************************************************************
//
//    SLP_B model 'slp_b_tsmc180bcd50_4kx12_cm16d_ab_r20'
//    OTP memory:
//      4Kx12 single ended
//      2Kx12 differential or ored
//      1Kx12 differential and ored
//    OTP array: 2x128x192, 48K bits, column mux 16
//    Version: v.2014.01.31
//    Release: v.1.14.11
//    Generated: Thu Aug 17 16:21:26 EDT 2017
//
//****************************************************************************

`resetall
`timescale 1ns/1ps
`celldefine
`ifdef verifault
	`suppress_faults
	`enable_portfaults
`endif
module slp_b_tsmc180bcd50_4kx12_cm16d_ab_r20(
		A,
		CK,
		D,
		MR,
		OE,
		Q,
		SEL,
		WE,
		VREF,
		EHV,
		VPP,
		VRR
		);
	parameter dataWidth = 12;
	parameter addressWidth = 12;
	parameter modeWidth = 8;
	parameter diffAvailable = 1'b1;
	parameter romContentFile = "";
	parameter MODE_READ_DIFF_BIT = 0;
	parameter MODE_READ_ORED_BIT = 4;
	input SEL;
	input CK;
	input [(addressWidth-1):0] A;
	input WE;
	input [(dataWidth-1):0] D;
	output [(dataWidth-1):0] Q;
	input OE;
	input [(modeWidth-1):0] MR;
	inout VREF;
	input EHV;
	inout VPP;
	inout VRR;
	wire SEL_i;
	wire CK_i;
	wire [(addressWidth-1):0] A_i;
	wire WE_i;
	wire [(dataWidth-1):0] D_i;
	wire [(dataWidth-1):0] Q_o;
	wire OE_i;
	wire [(modeWidth-1):0] MR_i;
	wire EHV_i;
	buf(EHV_i, EHV);
	buf(SEL_i, SEL);
	buf(CK_i, CK);
	buf(WE_i, WE);
	buf(OE_i, OE);
	buf(A_i[11], A[11]);
	buf(A_i[10], A[10]);
	buf(A_i[9], A[9]);
	buf(A_i[8], A[8]);
	buf(A_i[7], A[7]);
	buf(A_i[6], A[6]);
	buf(A_i[5], A[5]);
	buf(A_i[4], A[4]);
	buf(A_i[3], A[3]);
	buf(A_i[2], A[2]);
	buf(A_i[1], A[1]);
	buf(A_i[0], A[0]);
	buf(D_i[11], D[11]);
	buf(D_i[10], D[10]);
	buf(D_i[9], D[9]);
	buf(D_i[8], D[8]);
	buf(D_i[7], D[7]);
	buf(D_i[6], D[6]);
	buf(D_i[5], D[5]);
	buf(D_i[4], D[4]);
	buf(D_i[3], D[3]);
	buf(D_i[2], D[2]);
	buf(D_i[1], D[1]);
	buf(D_i[0], D[0]);
	buf(MR_i[7], MR[7]);
	buf(MR_i[6], MR[6]);
	buf(MR_i[5], MR[5]);
	buf(MR_i[4], MR[4]);
	buf(MR_i[3], MR[3]);
	buf(MR_i[2], MR[2]);
	buf(MR_i[1], MR[1]);
	buf(MR_i[0], MR[0]);
	nmos(Q[11], Q_o[11], 1'b1);
	nmos(Q[10], Q_o[10], 1'b1);
	nmos(Q[9], Q_o[9], 1'b1);
	nmos(Q[8], Q_o[8], 1'b1);
	nmos(Q[7], Q_o[7], 1'b1);
	nmos(Q[6], Q_o[6], 1'b1);
	nmos(Q[5], Q_o[5], 1'b1);
	nmos(Q[4], Q_o[4], 1'b1);
	nmos(Q[3], Q_o[3], 1'b1);
	nmos(Q[2], Q_o[2], 1'b1);
	nmos(Q[1], Q_o[1], 1'b1);
	nmos(Q[0], Q_o[0], 1'b1);
	always @(posedge CK_i) if(~EHV_i) $display("[%0t]:%m:<WARNING> Internal power is off, operation ignored", $realtime);
	SLP_B_CORE_slp_b_tsmc180bcd50_4kx12_cm16d_ab_r20 core(
			.SEL(SEL_i),
			.CK(CK_i),
			.A(A_i),
			.WE(WE_i),
			.D(D_i),
			.Q(Q_o),
			.OE(OE_i),
			.VREF(VREF),
			.MR(MR_i),
			.VPP(VPP),
			.VRR(VRR)
		);
	wire SEL_EQ_1_AND_WE_EQ_1;
	wire SEL_EQ_1_AND_WE_EQ_0_AND_DIFF_EQ_0_AND_ORED_EQ_0;
	wire SEL_EQ_1_AND_WE_EQ_0_AND_DIFF_EQ_1_AND_ORED_EQ_0;
	wire SEL_EQ_1_AND_WE_EQ_0_AND_DIFF_EQ_0_AND_ORED_EQ_1;
	wire SEL_EQ_1_AND_WE_EQ_0_AND_DIFF_EQ_1_AND_ORED_EQ_1;
	reg PGM_;
	wire PGM;
	assign SEL_EQ_1_AND_WE_EQ_1 = SEL & WE;
	assign SEL_EQ_1_AND_WE_EQ_0_AND_DIFF_EQ_0_AND_ORED_EQ_0 = SEL & ~WE & ~MR[MODE_READ_DIFF_BIT] & ~MR[MODE_READ_ORED_BIT];
	assign SEL_EQ_1_AND_WE_EQ_0_AND_DIFF_EQ_1_AND_ORED_EQ_0 = SEL & ~WE &  MR[MODE_READ_DIFF_BIT] & ~MR[MODE_READ_ORED_BIT];
	assign SEL_EQ_1_AND_WE_EQ_0_AND_DIFF_EQ_0_AND_ORED_EQ_1 = SEL & ~WE & ~MR[MODE_READ_DIFF_BIT] &  MR[MODE_READ_ORED_BIT];
	assign SEL_EQ_1_AND_WE_EQ_0_AND_DIFF_EQ_1_AND_ORED_EQ_1 = SEL & ~WE &  MR[MODE_READ_DIFF_BIT] &  MR[MODE_READ_ORED_BIT];
	always @(posedge CK) PGM_ <= SEL_EQ_1_AND_WE_EQ_1;
	assign PGM = PGM_;
	reg notifier;
	specify
		specparam tPP = 100000.0:100000.0:100000.0;
		specparam tPR = 100.0:100.0:100.0;
		specparam tWP = 100.0:100.0:200.0;
		specparam tWS = 11.0:16.0:25.0;
		specparam tSP = 100.0:100.0:200.0;
		specparam tVPPS = 100.0:100.0:200.0;
		specparam tVPPH = 20.0:20.0:20.0;
		specparam tRP = 15.0:23.0:43.0;
		specparam tRP_DIFF = 6.0:11.0:20.0;
		specparam tRPR = 5.0:9.0:18.0;
		specparam tRPR_DIFF = 4.0:6.0:13.0;
		specparam tRR = 4.0:6.0:12.0;
		specparam tRACC = 1.0:1.4:2.3;
		specparam tVRRS = 3000.0:3000.0:3000.0;
		specparam tVRRH = 50.0:50.0:50.0;
		specparam tLOAD = 0.6:1.0:1.7;
		specparam tSS = 4.0:6.0:11.0;
		specparam tRP_MAX = 2000.0:2000.0:2000.0;
		specparam tAS = 3.0:6.0:11.0;
		specparam tAH = 1.0:1.0:2.0;
		specparam tDS = 1.0:1.0:1.0;
		specparam tDH = 1.0:1.0:2.0;
		specparam tWH = 1.0:1.0:2.0;
		specparam tSH = 1.0:1.0:1.0;
		specparam tMRS = 5.0:6.0:10.0;
		specparam tMRH = 4.0:5.0:9.0;
		specparam tQACC = 0.2:0.3:0.4;
		specparam tQH = 0.3:0.4:0.5;
		specparam tES = 3000.0:3000.0:3000.0;
		specparam tEH = 50.0:50.0:50.0;
		specparam tpw_CK_posedge_SEL_EQ_1_AND_WE_EQ_1 = tPP;
		specparam tpw_CK_posedge_SEL_EQ_1_AND_WE_EQ_0_AND_DIFF_EQ_0_AND_ORED_EQ_0 = tRP;
		specparam tpw_CK_posedge_SEL_EQ_1_AND_WE_EQ_0_AND_DIFF_EQ_1_AND_ORED_EQ_0 = tRP_DIFF;
		specparam tpw_CK_posedge_SEL_EQ_1_AND_WE_EQ_0_AND_DIFF_EQ_0_AND_ORED_EQ_1 = tRPR;
		specparam tpw_CK_posedge_SEL_EQ_1_AND_WE_EQ_0_AND_DIFF_EQ_1_AND_ORED_EQ_1 = tRPR_DIFF;
		specparam tpw_CK_negedge_PGM_EQ_1 = tPR;
		specparam tpw_CK_negedge_PGM_EQ_0 = tRR;
		specparam tsetup_CK_SEL_posedge_posedge_WE_EQ_1 = tSP;
		specparam tsetup_CK_SEL_posedge_negedge_WE_EQ_1 = tSS;
		specparam tsetup_CK_SEL_posedge_posedge_WE_EQ_0 = tSS;
		specparam tsetup_CK_SEL_posedge_negedge_WE_EQ_0 = tSS;
		specparam thold_CK_SEL_posedge_noedge = tSH;
		specparam tsetup_CK_WE_posedge_posedge_SEL_EQ_1 = tWP;
		specparam tsetup_CK_WE_posedge_negedge_SEL_EQ_1 = tWS;
		specparam thold_CK_WE_posedge_noedge_SEL_EQ_1 = tWH;
		specparam tsetup_CK_A_posedge_noedge_SEL_EQ_1 = tAS;
		specparam thold_CK_A_posedge_noedge_SEL_EQ_1 = tAH;
		specparam tsetup_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1 = tDS;
		specparam thold_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1 = tDH;
		specparam tncsetup_CK_VPP_posedge_posedge = tVPPS;
		specparam tnchold_CK_VPP_posedge_posedge = tVPPH;
		specparam tncsetup_CK_VRR_posedge_posedge = tVRRS;
		specparam tnchold_CK_VRR_posedge_posedge = tVRRH;
		specparam tncsetup_CK_MR_posedge_noedge = tMRS;
		specparam tnchold_CK_MR_posedge_noedge = tMRH;
		specparam tpd_CK_Q_negedge_noedge = tRACC;
		specparam ttr_CK_Q_negedge_noedge = tLOAD;
		specparam tpd_OE_Q_posedge_noedge = tQACC;
		specparam tpd_OE_Q_negedge_noedge = tQH;
		specparam ttr_OE_Q_posedge_noedge = tLOAD;
		specparam ttr_OE_Q_negedge_noedge = tLOAD;
		specparam tncsetup_CK_EHV_posedge_noedge = tES;
		specparam tnchold_CK_EHV_posedge_noedge = tEH;
		specparam tncsetup_SEL_EHV_posedge_noedge = tES;
		specparam tnchold_SEL_EHV_posedge_noedge = tEH;
		specparam tncsetup_WE_EHV_posedge_noedge = tES;
		specparam tnchold_WE_EHV_posedge_noedge = tEH;
		specparam tncsetup_VPP_EHV_posedge_noedge = tES;
		specparam tnchold_VPP_EHV_posedge_noedge = tEH;
		$width(posedge CK &&& SEL_EQ_1_AND_WE_EQ_1, tpw_CK_posedge_SEL_EQ_1_AND_WE_EQ_1, 0, notifier);
		$width(posedge CK &&& SEL_EQ_1_AND_WE_EQ_0_AND_DIFF_EQ_0_AND_ORED_EQ_0, tpw_CK_posedge_SEL_EQ_1_AND_WE_EQ_0_AND_DIFF_EQ_0_AND_ORED_EQ_0, 0, notifier);
		$width(posedge CK &&& SEL_EQ_1_AND_WE_EQ_0_AND_DIFF_EQ_1_AND_ORED_EQ_0, tpw_CK_posedge_SEL_EQ_1_AND_WE_EQ_0_AND_DIFF_EQ_1_AND_ORED_EQ_0, 0, notifier);
		$width(posedge CK &&& SEL_EQ_1_AND_WE_EQ_0_AND_DIFF_EQ_0_AND_ORED_EQ_1, tpw_CK_posedge_SEL_EQ_1_AND_WE_EQ_0_AND_DIFF_EQ_0_AND_ORED_EQ_1, 0, notifier);
		$width(posedge CK &&& SEL_EQ_1_AND_WE_EQ_0_AND_DIFF_EQ_1_AND_ORED_EQ_1, tpw_CK_posedge_SEL_EQ_1_AND_WE_EQ_0_AND_DIFF_EQ_1_AND_ORED_EQ_1, 0, notifier);
		$width(negedge CK &&& PGM, tpw_CK_negedge_PGM_EQ_1, 0, notifier);
		$width(negedge CK &&& ~PGM, tpw_CK_negedge_PGM_EQ_0, 0, notifier);
		$setup(posedge SEL, posedge CK &&& WE, tsetup_CK_SEL_posedge_posedge_WE_EQ_1, notifier);
		$setup(negedge SEL, posedge CK &&& WE, tsetup_CK_SEL_posedge_negedge_WE_EQ_1, notifier);
		$setup(posedge SEL, posedge CK &&& ~WE, tsetup_CK_SEL_posedge_posedge_WE_EQ_0, notifier);
		$setup(negedge SEL, posedge CK &&& ~WE, tsetup_CK_SEL_posedge_negedge_WE_EQ_0, notifier);
		$hold(posedge CK &&& WE, posedge SEL, thold_CK_SEL_posedge_noedge, notifier);
		$hold(posedge CK &&& WE, negedge SEL, thold_CK_SEL_posedge_noedge, notifier);
		$hold(posedge CK &&& ~WE, posedge SEL, thold_CK_SEL_posedge_noedge, notifier);
		$hold(posedge CK &&& ~WE, negedge SEL, thold_CK_SEL_posedge_noedge, notifier);
		$setuphold(posedge CK &&& SEL, posedge WE, tsetup_CK_WE_posedge_posedge_SEL_EQ_1, thold_CK_WE_posedge_noedge_SEL_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL, negedge WE, tsetup_CK_WE_posedge_negedge_SEL_EQ_1, thold_CK_WE_posedge_noedge_SEL_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL, posedge A[11], tsetup_CK_A_posedge_noedge_SEL_EQ_1, thold_CK_A_posedge_noedge_SEL_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL, posedge A[10], tsetup_CK_A_posedge_noedge_SEL_EQ_1, thold_CK_A_posedge_noedge_SEL_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL, posedge A[9], tsetup_CK_A_posedge_noedge_SEL_EQ_1, thold_CK_A_posedge_noedge_SEL_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL, posedge A[8], tsetup_CK_A_posedge_noedge_SEL_EQ_1, thold_CK_A_posedge_noedge_SEL_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL, posedge A[7], tsetup_CK_A_posedge_noedge_SEL_EQ_1, thold_CK_A_posedge_noedge_SEL_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL, posedge A[6], tsetup_CK_A_posedge_noedge_SEL_EQ_1, thold_CK_A_posedge_noedge_SEL_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL, posedge A[5], tsetup_CK_A_posedge_noedge_SEL_EQ_1, thold_CK_A_posedge_noedge_SEL_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL, posedge A[4], tsetup_CK_A_posedge_noedge_SEL_EQ_1, thold_CK_A_posedge_noedge_SEL_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL, posedge A[3], tsetup_CK_A_posedge_noedge_SEL_EQ_1, thold_CK_A_posedge_noedge_SEL_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL, posedge A[2], tsetup_CK_A_posedge_noedge_SEL_EQ_1, thold_CK_A_posedge_noedge_SEL_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL, posedge A[1], tsetup_CK_A_posedge_noedge_SEL_EQ_1, thold_CK_A_posedge_noedge_SEL_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL, posedge A[0], tsetup_CK_A_posedge_noedge_SEL_EQ_1, thold_CK_A_posedge_noedge_SEL_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL, negedge A[11], tsetup_CK_A_posedge_noedge_SEL_EQ_1, thold_CK_A_posedge_noedge_SEL_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL, negedge A[10], tsetup_CK_A_posedge_noedge_SEL_EQ_1, thold_CK_A_posedge_noedge_SEL_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL, negedge A[9], tsetup_CK_A_posedge_noedge_SEL_EQ_1, thold_CK_A_posedge_noedge_SEL_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL, negedge A[8], tsetup_CK_A_posedge_noedge_SEL_EQ_1, thold_CK_A_posedge_noedge_SEL_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL, negedge A[7], tsetup_CK_A_posedge_noedge_SEL_EQ_1, thold_CK_A_posedge_noedge_SEL_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL, negedge A[6], tsetup_CK_A_posedge_noedge_SEL_EQ_1, thold_CK_A_posedge_noedge_SEL_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL, negedge A[5], tsetup_CK_A_posedge_noedge_SEL_EQ_1, thold_CK_A_posedge_noedge_SEL_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL, negedge A[4], tsetup_CK_A_posedge_noedge_SEL_EQ_1, thold_CK_A_posedge_noedge_SEL_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL, negedge A[3], tsetup_CK_A_posedge_noedge_SEL_EQ_1, thold_CK_A_posedge_noedge_SEL_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL, negedge A[2], tsetup_CK_A_posedge_noedge_SEL_EQ_1, thold_CK_A_posedge_noedge_SEL_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL, negedge A[1], tsetup_CK_A_posedge_noedge_SEL_EQ_1, thold_CK_A_posedge_noedge_SEL_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL, negedge A[0], tsetup_CK_A_posedge_noedge_SEL_EQ_1, thold_CK_A_posedge_noedge_SEL_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL_EQ_1_AND_WE_EQ_1, posedge D[11], tsetup_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, thold_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL_EQ_1_AND_WE_EQ_1, posedge D[10], tsetup_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, thold_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL_EQ_1_AND_WE_EQ_1, posedge D[9], tsetup_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, thold_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL_EQ_1_AND_WE_EQ_1, posedge D[8], tsetup_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, thold_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL_EQ_1_AND_WE_EQ_1, posedge D[7], tsetup_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, thold_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL_EQ_1_AND_WE_EQ_1, posedge D[6], tsetup_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, thold_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL_EQ_1_AND_WE_EQ_1, posedge D[5], tsetup_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, thold_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL_EQ_1_AND_WE_EQ_1, posedge D[4], tsetup_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, thold_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL_EQ_1_AND_WE_EQ_1, posedge D[3], tsetup_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, thold_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL_EQ_1_AND_WE_EQ_1, posedge D[2], tsetup_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, thold_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL_EQ_1_AND_WE_EQ_1, posedge D[1], tsetup_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, thold_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL_EQ_1_AND_WE_EQ_1, posedge D[0], tsetup_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, thold_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL_EQ_1_AND_WE_EQ_1, negedge D[11], tsetup_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, thold_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL_EQ_1_AND_WE_EQ_1, negedge D[10], tsetup_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, thold_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL_EQ_1_AND_WE_EQ_1, negedge D[9], tsetup_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, thold_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL_EQ_1_AND_WE_EQ_1, negedge D[8], tsetup_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, thold_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL_EQ_1_AND_WE_EQ_1, negedge D[7], tsetup_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, thold_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL_EQ_1_AND_WE_EQ_1, negedge D[6], tsetup_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, thold_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL_EQ_1_AND_WE_EQ_1, negedge D[5], tsetup_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, thold_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL_EQ_1_AND_WE_EQ_1, negedge D[4], tsetup_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, thold_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL_EQ_1_AND_WE_EQ_1, negedge D[3], tsetup_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, thold_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL_EQ_1_AND_WE_EQ_1, negedge D[2], tsetup_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, thold_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL_EQ_1_AND_WE_EQ_1, negedge D[1], tsetup_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, thold_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, notifier);
		$setuphold(posedge CK &&& SEL_EQ_1_AND_WE_EQ_1, negedge D[0], tsetup_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, thold_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1, notifier);
		$nochange(posedge CK, posedge VPP, tncsetup_CK_VPP_posedge_posedge, tnchold_CK_VPP_posedge_posedge);
		$nochange(posedge CK, posedge VRR, tncsetup_CK_VRR_posedge_posedge, tnchold_CK_VRR_posedge_posedge);
		$nochange(posedge CK, posedge MR[7], tncsetup_CK_MR_posedge_noedge, tnchold_CK_MR_posedge_noedge);
		$nochange(posedge CK, posedge MR[6], tncsetup_CK_MR_posedge_noedge, tnchold_CK_MR_posedge_noedge);
		$nochange(posedge CK, posedge MR[5], tncsetup_CK_MR_posedge_noedge, tnchold_CK_MR_posedge_noedge);
		$nochange(posedge CK, posedge MR[4], tncsetup_CK_MR_posedge_noedge, tnchold_CK_MR_posedge_noedge);
		$nochange(posedge CK, posedge MR[3], tncsetup_CK_MR_posedge_noedge, tnchold_CK_MR_posedge_noedge);
		$nochange(posedge CK, posedge MR[2], tncsetup_CK_MR_posedge_noedge, tnchold_CK_MR_posedge_noedge);
		$nochange(posedge CK, posedge MR[1], tncsetup_CK_MR_posedge_noedge, tnchold_CK_MR_posedge_noedge);
		$nochange(posedge CK, posedge MR[0], tncsetup_CK_MR_posedge_noedge, tnchold_CK_MR_posedge_noedge);
		$nochange(posedge CK, negedge MR[7], tncsetup_CK_MR_posedge_noedge, tnchold_CK_MR_posedge_noedge);
		$nochange(posedge CK, negedge MR[6], tncsetup_CK_MR_posedge_noedge, tnchold_CK_MR_posedge_noedge);
		$nochange(posedge CK, negedge MR[5], tncsetup_CK_MR_posedge_noedge, tnchold_CK_MR_posedge_noedge);
		$nochange(posedge CK, negedge MR[4], tncsetup_CK_MR_posedge_noedge, tnchold_CK_MR_posedge_noedge);
		$nochange(posedge CK, negedge MR[3], tncsetup_CK_MR_posedge_noedge, tnchold_CK_MR_posedge_noedge);
		$nochange(posedge CK, negedge MR[2], tncsetup_CK_MR_posedge_noedge, tnchold_CK_MR_posedge_noedge);
		$nochange(posedge CK, negedge MR[1], tncsetup_CK_MR_posedge_noedge, tnchold_CK_MR_posedge_noedge);
		$nochange(posedge CK, negedge MR[0], tncsetup_CK_MR_posedge_noedge, tnchold_CK_MR_posedge_noedge);
		(negedge CK => (Q[11] : 'bx)) = (tpd_CK_Q_negedge_noedge, tpd_CK_Q_negedge_noedge);
		(negedge CK => (Q[10] : 'bx)) = (tpd_CK_Q_negedge_noedge, tpd_CK_Q_negedge_noedge);
		(negedge CK => (Q[9] : 'bx)) = (tpd_CK_Q_negedge_noedge, tpd_CK_Q_negedge_noedge);
		(negedge CK => (Q[8] : 'bx)) = (tpd_CK_Q_negedge_noedge, tpd_CK_Q_negedge_noedge);
		(negedge CK => (Q[7] : 'bx)) = (tpd_CK_Q_negedge_noedge, tpd_CK_Q_negedge_noedge);
		(negedge CK => (Q[6] : 'bx)) = (tpd_CK_Q_negedge_noedge, tpd_CK_Q_negedge_noedge);
		(negedge CK => (Q[5] : 'bx)) = (tpd_CK_Q_negedge_noedge, tpd_CK_Q_negedge_noedge);
		(negedge CK => (Q[4] : 'bx)) = (tpd_CK_Q_negedge_noedge, tpd_CK_Q_negedge_noedge);
		(negedge CK => (Q[3] : 'bx)) = (tpd_CK_Q_negedge_noedge, tpd_CK_Q_negedge_noedge);
		(negedge CK => (Q[2] : 'bx)) = (tpd_CK_Q_negedge_noedge, tpd_CK_Q_negedge_noedge);
		(negedge CK => (Q[1] : 'bx)) = (tpd_CK_Q_negedge_noedge, tpd_CK_Q_negedge_noedge);
		(negedge CK => (Q[0] : 'bx)) = (tpd_CK_Q_negedge_noedge, tpd_CK_Q_negedge_noedge);
		(OE => Q[11]) = (0.0, 0.0, tpd_OE_Q_negedge_noedge, tpd_OE_Q_posedge_noedge, tpd_OE_Q_negedge_noedge, tpd_OE_Q_posedge_noedge);
		(OE => Q[10]) = (0.0, 0.0, tpd_OE_Q_negedge_noedge, tpd_OE_Q_posedge_noedge, tpd_OE_Q_negedge_noedge, tpd_OE_Q_posedge_noedge);
		(OE => Q[9]) = (0.0, 0.0, tpd_OE_Q_negedge_noedge, tpd_OE_Q_posedge_noedge, tpd_OE_Q_negedge_noedge, tpd_OE_Q_posedge_noedge);
		(OE => Q[8]) = (0.0, 0.0, tpd_OE_Q_negedge_noedge, tpd_OE_Q_posedge_noedge, tpd_OE_Q_negedge_noedge, tpd_OE_Q_posedge_noedge);
		(OE => Q[7]) = (0.0, 0.0, tpd_OE_Q_negedge_noedge, tpd_OE_Q_posedge_noedge, tpd_OE_Q_negedge_noedge, tpd_OE_Q_posedge_noedge);
		(OE => Q[6]) = (0.0, 0.0, tpd_OE_Q_negedge_noedge, tpd_OE_Q_posedge_noedge, tpd_OE_Q_negedge_noedge, tpd_OE_Q_posedge_noedge);
		(OE => Q[5]) = (0.0, 0.0, tpd_OE_Q_negedge_noedge, tpd_OE_Q_posedge_noedge, tpd_OE_Q_negedge_noedge, tpd_OE_Q_posedge_noedge);
		(OE => Q[4]) = (0.0, 0.0, tpd_OE_Q_negedge_noedge, tpd_OE_Q_posedge_noedge, tpd_OE_Q_negedge_noedge, tpd_OE_Q_posedge_noedge);
		(OE => Q[3]) = (0.0, 0.0, tpd_OE_Q_negedge_noedge, tpd_OE_Q_posedge_noedge, tpd_OE_Q_negedge_noedge, tpd_OE_Q_posedge_noedge);
		(OE => Q[2]) = (0.0, 0.0, tpd_OE_Q_negedge_noedge, tpd_OE_Q_posedge_noedge, tpd_OE_Q_negedge_noedge, tpd_OE_Q_posedge_noedge);
		(OE => Q[1]) = (0.0, 0.0, tpd_OE_Q_negedge_noedge, tpd_OE_Q_posedge_noedge, tpd_OE_Q_negedge_noedge, tpd_OE_Q_posedge_noedge);
		(OE => Q[0]) = (0.0, 0.0, tpd_OE_Q_negedge_noedge, tpd_OE_Q_posedge_noedge, tpd_OE_Q_negedge_noedge, tpd_OE_Q_posedge_noedge);
		$nochange(posedge CK, posedge EHV, tncsetup_CK_EHV_posedge_noedge, tnchold_CK_EHV_posedge_noedge);
		$nochange(posedge SEL, posedge EHV, tncsetup_SEL_EHV_posedge_noedge, tnchold_SEL_EHV_posedge_noedge);
		$nochange(posedge WE, posedge EHV, tncsetup_WE_EHV_posedge_noedge, tnchold_WE_EHV_posedge_noedge);
		$nochange(posedge VPP, posedge EHV, tncsetup_VPP_EHV_posedge_noedge, tnchold_VPP_EHV_posedge_noedge);
	endspecify
	task info;
		core.info;
	endtask
	task cleanOtp;
		core.cleanOtp;
	endtask
	task readOtp;
		input [((256*8)-1):0] path;
		begin
			$readmemh(path, core.otp);
		end
	endtask
	task writeOtp;
		input [((256*8)-1):0] path;
		begin
			$writememh(path, core.otp);
		end
	endtask
	task cleanRom;
		core.cleanRom;
	endtask
	task readRom;
		input [((256*8)-1):0] path;
		begin
			$readmemh(path, core.rom);
		end
	endtask
	task writeRom;
		input [((256*8)-1):0] path;
		begin
			$writememh(path, core.rom);
		end
	endtask
	task cleanErr;
		core.cleanErr;
	endtask
	task stuckAtOne;
		input [(addressWidth-1):0] addr;
		input [(dataWidth-1):0] data;
		reg [(dataWidth-1):0] e;
		integer i;
		begin
			e = core.err[addr];
			for(i=0;i<dataWidth;i=i+1) if(data[i] === 1'b1) e[i] = 1'b1;
			core.err[addr] = e;
		end
	endtask
	task stuckAtZero;
		input [(addressWidth-1):0] addr;
		input [(dataWidth-1):0] data;
		reg [(dataWidth-1):0] e;
		integer i;
		begin
			e = core.err[addr];
			for(i=0;i<dataWidth;i=i+1) if(data[i] === 1'b1) e[i] = 1'b0;
			core.err[addr] = e;
		end
	endtask
	initial begin : initRom
		if(romContentFile != "") readRom(romContentFile);
	end
endmodule
`endcelldefine
`ifdef verifault
	`disable_portfaults
	`nosuppress_faults
`endif
module SLP_B_CORE_slp_b_tsmc180bcd50_4kx12_cm16d_ab_r20(
		SEL,
		CK,
		A,
		WE,
		D,
		Q,
		OE,
		VREF,
		MR,
		VPP,
		VRR
		);
	parameter dataWidth = 12;
	parameter addressWidth = 12;
	parameter modeWidth = 8;
	parameter diffAddressBit = 5;
	parameter oredAddressBit = 6;
	parameter diffAvailable = 1'b1;
	parameter oneArray = 1'b0;
	parameter tpw_PGM = 100000.0:100000.0:100000.0;
	parameter trecovery_PGM = 100.0:100.0:100.0;
	parameter tpw_RD = 15.0:23.0:43.0;
	parameter tpw_RD_DIFF = 6.0:11.0:20.0;
	parameter tpw_RD_ORED = 5.0:9.0:18.0;
	parameter tpw_RD_DIFF_ORED = 4.0:6.0:13.0;
	parameter trecovery_RD = 4.0:6.0:12.0;
	parameter tRP_MAX = 2000.0:2000.0:2000.0;
	parameter defaultProgramMin = 1;
	parameter defaultProgramMax = 1;
	parameter defaultProgrammability = -1;
	parameter defaultTouchX = 1'bx;
	parameter defaultDisplayError   = 1;
	parameter defaultDisplayWarning = 1;
	parameter defaultDisplayInfo    = 0;
	parameter defaultDisplayDebug   = 0;
	parameter MODE_READ_DIFF_BIT = 0;
	parameter MODE_READ_ORED_BIT = 4;
	parameter MODE_READ_VERF_BIT = 6;
	parameter MODE_TEST_WL_BIT = 1;
	parameter MODE_TEST_BL_BIT = 2;
	parameter MODE_TEST_SAP_BIT = 3;
	parameter MODE_TEST_SAN_BIT = 5;
	parameter MODE_TEST_CC_BIT = 7;
	parameter words = 4096;
	parameter bits = words * dataWidth;
	parameter numberOfWordsPerRow = 16;
	parameter numberOfRows = words / numberOfWordsPerRow;
	parameter numberOfColumns = numberOfWordsPerRow * dataWidth;
	parameter [(addressWidth-1):0] diffAddrMask = 1 << diffAddressBit;
	parameter [(addressWidth-1):0] oredAddrMask = 1 << oredAddressBit;
	input SEL;
	input CK;
	input [(addressWidth-1):0] A;
	input WE;
	input [(dataWidth-1):0] D;
	output [(dataWidth-1):0] Q;
	input OE;
	input [(modeWidth-1):0] MR;
	inout VREF;
	inout VPP;
	inout VRR;
	reg WE_FF;
	reg [(dataWidth-1):0] D_FF;
	reg [(addressWidth-1):0] A_FF;
	reg unknownAddress;
	reg addressExists;
	reg [(dataWidth-1):0] Q_;
	reg [(dataWidth-1):0] otp[0:(words-1)];
	reg [(dataWidth-1):0] rom[0:(words-1)];
	reg [(dataWidth-1):0] err[0:(words-1)];
	integer programMin;
	integer programMax;
	integer programmability;
	reg touchX;
	integer vppPower;
	event startPGM;
	reg PGM;
	event startRD;
	reg RD;
	reg recovery;
	reg SEL_FF;
	reg CK_;
	wire STB;
	reg lastSTB;
	reg [(addressWidth-1):0] addr;
	reg [(dataWidth-1):0] data;
	wire slp_ref;
	wire [(modeWidth-1):0] mode;
	reg mode_OK;
	reg VRR_OK;
	reg VPP_OK;
	wire TEST_CC, TEST_SAN, TEST_SAP, TEST_BL, TEST_WL, VERIFY, ORED, DIFF;
	assign {TEST_CC, VERIFY, TEST_SAN, ORED, TEST_SAP, TEST_BL, TEST_WL, DIFF} = MR;
	assign mode = MR;
	always @(VRR) if(RD) VRR_OK = 1'b0;
	always @(VPP) if(PGM) VPP_OK = 1'b0;
	always @(mode) if(PGM | RD) mode_OK = 1'b0;
	assign Q = OE ? Q_ : {dataWidth{1'bz}};
	assign slp_ref = (VERIFY === 1'b1) ? VREF : (VERIFY === 1'b0) ? 1'b1 : 1'bx;
	
	reg	test_trp_max;
	
	initial begin : init
		programMin = defaultProgramMin;
		programMax = defaultProgramMax;
		programmability = defaultProgrammability;
		touchX = defaultTouchX;
		cleanOtp;
		recovery = 1'b0;
		if(defaultDisplayInfo) info;
		test_trp_max = 1'b1;
	end
	task info;
		begin
			$display("\n%m:<INFO>: SLP structure");
			$write("  memory - %0dx%0d", words, dataWidth);
			$write  (" single ended");
			$write (" / %0dx%0d redundant", words >> 1, dataWidth);
			if(diffAvailable) $display(" / %0dx%0d differential", words >> 1, dataWidth); else $display("");
			$write("  array  - ");
			if(diffAvailable) $write("2x%0dx%0d", numberOfRows >> 1, numberOfColumns);
			else $write("%0dx%0d", numberOfRows, numberOfColumns);
			$display(", %0d bits, column mux %0d", bits, numberOfWordsPerRow);
		end
	endtask
	always @(posedge CK) begin
		SEL_FF <= SEL;
		if(SEL) begin
			D_FF <= D;
			A_FF <= A;
			WE_FF <= WE;
			unknownAddress = (^A === 1'bx);
			addressExists = (int'(A) <= (words-1));
		end
	end
	always @(CK)
	begin
		#(0.001);
		CK_ = CK;
	end
	wire readPulse;
	real readMaxTime;
	assign readPulse = SEL_FF & (!WE_FF) & CK_ ;
	always @ (readPulse)
		if (readPulse) readMaxTime = $realtime;
		else begin
			if (test_trp_max == 1'b1) begin
				if (($realtime - readMaxTime) > tRP_MAX) begin
					disable read;
					$display("[%0t]:%m:<WARNING> Maximum read time (tRP_MAX) violation", $time);
					#(0.001) Q_ = data | {dataWidth{1'bx}};
				end
			end
		end
	assign STB = SEL_FF & CK_;
	always @(STB) lastSTB <= STB;
	always @(startPGM) begin : pulsePGM
		PGM = 1'b1;
		#(tpw_PGM - 0.01) PGM = 1'b0;
	end
	always @(negedge STB) if(PGM) begin
			disable write;
			if(defaultDisplayWarning) $display("[%0t]:%m:<WARNING> Program time violation", $time);
			disable pulsePGM;
			PGM = 1'b0;
		end
	always @(negedge PGM) begin
		recovery = 1'b1;
		#(trecovery_PGM - 0.01) recovery = 1'b0;
	end
	always @(startRD) begin : pulseRD
		RD = 1'b1;
		case({ORED, DIFF})
			2'b00 : #(tpw_RD - 0.01);
			2'b01 : #(tpw_RD_DIFF - 0.01);
			2'b10 : #(tpw_RD_ORED - 0.01);
			2'b11 : #(tpw_RD_DIFF_ORED - 0.01);
		endcase
		RD = 1'b0;
	end
	always @(negedge STB) if(RD) begin
			disable read;
			if(defaultDisplayWarning) $display("[%0t]:%m:<WARNING> Read time violation", $time);
			disable pulseRD;
			RD = 1'b0;
			#(0.001) Q_ = {dataWidth{1'bx}};
		end
	always @(negedge RD) begin
		recovery = 1'b1;
		#(trecovery_RD - 0.01) recovery = 1'b0;
	end
	always @(posedge STB) if(recovery) begin
			if(WE !== 1'b0) memX({dataWidth{1'bx}});
			Q_ = {dataWidth{1'bx}};
			if(defaultDisplayWarning) $display("[%0t]:%m:<WARNING> Recovery time violation", $time);
		end
	always @(STB) if(recovery !== 1'b1) begin
			if(STB === 1'b1) begin
				if(lastSTB === 1'b0) begin
					if(SEL === 1'b1) begin
						if(WE === 1'b0) begin
							addr = A_FF;
							-> startRD;
							read;
						end else if(WE === 1'b1) begin
							addr = A_FF;
							if(~addressExists) begin
								if(defaultDisplayWarning) $display("[%0t]:%m:<WARNING> Can not program: address 0x%h doesn't exist", $time, addr);
							end else begin
								data = D_FF;
								-> startPGM;
								write;
							end
						end else begin
							if(unknownAddress) begin
								memX(D_FF);
								if(defaultDisplayWarning) $display("[%0t]:%m:<WARNING> Unknown access of unknown address", $time);
							end else begin
								otp[A_FF] = otp[A_FF] | (D_FF & {dataWidth{1'bx}});
								if(defaultDisplayWarning) $display("[%0t]:%m:<WARNING> Unknown access of known address", $time);
							end
						end
					end else if(SEL !== 1'b0) begin
						if(WE === 1'b0) begin
							@(STB) Q_ = {dataWidth{1'bx}};
							if(defaultDisplayWarning) $display("[%0t]:%m:<WARNING> Read with unknown select", $time);
						end else if(WE === 1'b1) begin
							if(unknownAddress) begin
								memX(D_FF);
								if(defaultDisplayWarning) $display("[%0t]:%m:<WARNING> Write with unknown select to an unknown address", $time);
							end else begin
								otp[A_FF] = otp[A_FF] | (D_FF & {dataWidth{1'bx}});
								if(defaultDisplayWarning) $display("[%0t]:%m:<WARNING> Write with unknown select to a known address", $time);
							end
						end else begin
							if(unknownAddress) begin
								memX(D_FF);
								if(defaultDisplayWarning) $display("[%0t]:%m:<WARNING> Unknown access with unknown select of unknown address", $time);
							end else begin
								otp[A_FF] = otp[A_FF] | (D_FF & {dataWidth{1'bx}});
								if(defaultDisplayWarning) $display("[%0t]:%m:<WARNING> Unknown access with unknown select of known address", $time);
							end
						end
					end
				end
			end else if(STB !== 1'b0) begin
				if(defaultDisplayError) $display("[%0t]:%m:<ERROR> Invalid SEL or CK", $time);
			end
		end
	function [(dataWidth-1):0] readMem;
		input [(addressWidth-1):0] a;
		reg [(dataWidth-1):0] d, r, e;
		integer i;
		begin
			d = otp[a];
			r = rom[a];
			e = err[a];
			for(i=0;i<dataWidth;i=i+1) if(e[i] !== 1'bx) d[i] = e[i]; else if(r[i] !== 1'bx) d[i] = r[i];
			readMem = d;
		end
	endfunction
	task read;
		reg [(dataWidth-1):0] q0;
		reg [(dataWidth-1):0] q1;
		integer i;
		begin
			mode_OK = (^mode !== 1'bx);
			VRR_OK = (VRR === 1'b1);
			if(mode_OK) case({TEST_SAN & slp_ref & ~DIFF, TEST_SAP})
					2'b00 : begin
						if (!VRR_OK) begin
							data = {dataWidth{1'bx}};
							if(defaultDisplayWarning) $display("[%0t]:%m:<WARNING> Invalid VRR", $time);
						end
						else if(DIFF === 1'b1) begin
							if(diffAvailable == 0) begin
								data = {dataWidth{1'bx}};
								if(defaultDisplayWarning) $display("[%0t]:%m:<WARNING> differential read mode is not available", $time);
							end
							else begin
								if(unknownAddress) begin
									data = {dataWidth{1'bx}};
									if(defaultDisplayWarning) $display("[%0t]:%m:<WARNING> Unknown address", $time);
								end
								else begin
									if(~addressExists) begin
										data = {dataWidth{1'bx}};
										if(defaultDisplayWarning) $display("[%0t]:%m:<WARNING> Address 0x%h doesn't exist", $time, addr);
									end
									else begin
										if(ORED === 1'b1) begin
											q0 = readMem((addr |  diffAddrMask) | oredAddrMask);
											q0 = q0 | readMem((addr |  diffAddrMask) & ~oredAddrMask);
											q1 = readMem((addr & ~diffAddrMask) | oredAddrMask);
											q1 = q1 | readMem((addr & ~diffAddrMask) & ~oredAddrMask);
										end else if(ORED === 1'b0) begin
											q0 = readMem(addr |  diffAddrMask);
											q1 = readMem(addr & ~diffAddrMask);
										end else begin
											q0 = {dataWidth{1'bx}};
											q1 = {dataWidth{1'bx}};
											if(defaultDisplayWarning) $display("[%0t]:%m:<WARNING> Unknown mode ored", $time);
										end
										for(i=0;i<dataWidth;i=i+1) data[i] = (q1[i] == ~q0[i]) ? q0[i] : 1'bx;
										if(oneArray) begin
											if(TEST_BL) data = {dataWidth{1'bx}};
											if(TEST_WL) data[(dataWidth - 1)] = 1'b1;
										end else begin
											if(TEST_BL) data = (addr & diffAddrMask) ? {dataWidth{1'b1}} : {dataWidth{1'b0}};
											if(TEST_WL) data[(dataWidth - 1)] = 1'bx;
										end
										if(defaultDisplayInfo) $display("[%0t]:%m:<INFO> @0x%h: %b as differential", $time, (addr & ~diffAddrMask), data);
									end
								end
							end
						end else if(DIFF === 1'b0) begin
							if(unknownAddress) begin
								data = {dataWidth{1'bx}};
								if(defaultDisplayWarning) $display("[%0t]:%m:<WARNING> Unknown address", $time);
							end else begin
								if(~addressExists) begin
									data = {dataWidth{1'b0}};
									if(defaultDisplayWarning) $display("[%0t]:%m:<WARNING> Address 0x%h doesn't exist", $time, addr);
								end else begin
									if(ORED === 1'b1) begin
										data = readMem(addr | oredAddrMask);
										data = data | readMem(addr & ~oredAddrMask);
									end else if(ORED === 1'b0) begin
										data = readMem(addr);
									end else begin
										data = {dataWidth{1'bx}};
										if(defaultDisplayWarning) $display("[%0t]:%m:<WARNING> Unknown mode ored", $time);
									end
									if(defaultDisplayInfo) $display("[%0t]:%m:<INFO> @0x%h: %b as normal", $time, addr, data);
								end
							end
							if(oneArray) begin
								if(TEST_WL & |(addr & diffAddrMask)) data[(dataWidth - 1)] = 1'b1;
							end else begin
								if(TEST_WL) data[(dataWidth - 1)] = 1'b1;
							end
							if(TEST_BL) data = {dataWidth{1'b1}};
						end else begin
							data = {dataWidth{1'bx}};
							if(defaultDisplayWarning) $display("[%0t]:%m:<WARNING> Unknown mode differential", $time);
						end
					end
					2'b01 : begin
						if(DIFF === 1'b0) begin
							data = {dataWidth{slp_ref}};
						end
						else if(DIFF === 1'b1) begin
							data = {dataWidth{slp_ref ? 1'b1 : 1'bx}};
						end
						else begin
							data = {dataWidth{1'bx}};
							if(defaultDisplayWarning) $display("[%0t]:%m:<WARNING> Unknown mode differential", $time);
						end
						if(defaultDisplayInfo) $display("[%0t]:%m:<INFO>: %b as test SAP", $time, data);
					end
					2'b10 : begin
						data = {dataWidth{1'b0}};
						if(defaultDisplayInfo) $display("[%0t]:%m:<INFO>: %b as test SAN normal (no DIFF, VREF high)", $time, data);
					end
					default : begin
						data = {dataWidth{1'bx}};
						if(defaultDisplayWarning) $display("[%0t]:%m:<WARNING> Invalid test mode", $time);
					end
				endcase
			@(STB);
			#(0.001) if(mode_OK) Q_ = data; else begin
				Q_ = {dataWidth{1'bx}};
			if(defaultDisplayWarning) $display("[%0t]:%m:<WARNING> Invalid mode", $time);
		end
		VRR_OK = 1'b0;
		mode_OK = 1'b0;
		end
	endtask
	task write;
		begin
			if(data === {dataWidth{1'b0}}) begin
				if(defaultDisplayInfo) $display(" zero program data");
				disable write;
			end
			mode_OK = (mode === 8'b0);
			VPP_OK = (VPP === 1'b1);
			if(~mode_OK) begin
				if(^addr[(addressWidth-2):0] === 1'bx) begin
					if(defaultDisplayWarning) $display("[%0t]:%m:<WARNING> Invalid mode with unknown address", $time);
					memX(data);
				end else begin
					if(defaultDisplayWarning) $display("[%0t]:%m:<WARNING> Invalid mode with known address", $time);
					otp[addr] = otp[addr |  diffAddrMask |  oredAddrMask] | (data & {dataWidth{1'bx}});
					otp[addr] = otp[addr |  diffAddrMask & ~oredAddrMask] | (data & {dataWidth{1'bx}});
					otp[addr] = otp[addr & ~diffAddrMask |  oredAddrMask] | (data & {dataWidth{1'bx}});
					otp[addr] = otp[addr & ~diffAddrMask & ~oredAddrMask] | (data & {dataWidth{1'bx}});
				end
			end else begin
				if(^addr === 1'bx) begin
					if(defaultDisplayWarning) $display("[%0t]:%m:<WARNING> Unknown address", $time);
					memX(data);
				end else begin
					if(touchX !== 1'b0) otp[addr] = otp[addr] | (data & {dataWidth{1'bx}});
					@(negedge recovery);
					if(VPP_OK & mode_OK) begin
						getVppPower;
						pgm;
					end else if(defaultDisplayWarning) $display("[%0t]:%m:<WARNING> Invalid VPP or mode", $time);
				end
			end
		end
	endtask
	task getVppPower;
		integer i;
		integer j;
		integer k;
		begin
			if(^programMax === 1'bx) programMax = dataWidth;
			if(programMax > dataWidth) programMax = dataWidth;
			if(programMax < 0) programMax = 1;
			if(^programMin === 1'bx) programMin = programMax;
			if(programMin > programMax) programMin = programMax;
			if(programMin < 0) programMin = 1;
			if(programMax > programMin) begin
				i = $random & 255;
				j = programMax - programMin + 1;
				k =  i / j;
				k = i - j * k;
			end else k = 0;
			vppPower = programMin + k;
			if(defaultDisplayDebug) $display("[%0t]:%m:<DEBUG> %0d", $time, vppPower);
		end
	endtask
	task pgm;
		integer i;
		integer j;
		integer k;
		reg [(dataWidth-1):0] temp;
		begin
			if(defaultDisplayInfo) $write("[%0t]:%m:<INFO> @0x%h:", $time, addr);
			if(defaultDisplayInfo) $display("\n    %b, data\n    %b, before", data, otp[addr]);
			temp = otp[addr];
			j = 0;
			k = 0;
			for(i=0;i<dataWidth;i=i+1) begin
				if(data[i] === 1'b1) begin
					k = k + 1;
					if(temp[i] === 1'b1) j = j + 1;
				end
			end
			if (j > 0) begin
				if(j == k) begin
					if(defaultDisplayDebug) $display("    All %0d required data bits already programmed", j);
					disable pgm;
				end
				if(vppPower <= j) begin
					if(defaultDisplayWarning) $display("[%0t]:%m:<WARNING> Can not program, unsufficient Vpp power %0d, %0d required data bits already programmed", $time, vppPower, j);
					vppPower = 0;
					disable pgm;
				end else begin
					vppPower = vppPower - j;
					if(defaultDisplayDebug) $display("    %0d required data bits already programmed, Vpp power %0d", j, vppPower);
				end
			end
			i = 0;
			j = 0;
			while((i < dataWidth) && ((j < vppPower))) begin
				if(data[i] & (temp[i] !== 1'b1)) begin
					if(programmability & $random) temp[i] = 1'b1;
					j = j + 1;
				end
				i = i + 1;
			end
			otp[addr] = temp;
			if(defaultDisplayDebug) $display("    %0d of %0d required data bits programmed", j, k);
			if(defaultDisplayInfo) $display("    %b, after", otp[addr]);
		end
	endtask
	task memX;
		input [(dataWidth-1):0] W;
		integer i;
		begin
			for (i=0;i<words;i=i+1) otp[i] = otp[i] | (W & {dataWidth{1'bx}});
		end
	endtask
	task cleanOtp;
		integer i;
		begin
			for (i=0;i<words;i=i+1) otp[i] = {dataWidth{1'b0}};
		end
	endtask
	task cleanRom;
		integer i;
		begin
			for (i=0;i<words;i=i+1) rom[i] = {dataWidth{1'bx}};
		end
	endtask
	task cleanErr;
		integer i;
		begin
			for (i=0;i<words;i=i+1) err[i] = {dataWidth{1'bx}};
		end
	endtask
endmodule
