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

`include "slp_b_tsmc180bcd50_4kx12_cm16d_ab_r20.v"
module SLP_B_TB;
parameter dataWidth = 12;
parameter addressWidth = 12;
parameter modeWidth = 8;
parameter YaddressWidth = 4;
parameter diffAvailable = 1'b1;
parameter romContentFile = "";
parameter diffAddressBit = 5;
parameter oredAddressBit = 6;
parameter XaddressWidth = (diffAvailable == 0) ? (addressWidth - YaddressWidth) : (addressWidth - YaddressWidth - 1);
parameter numberOfRows = (diffAvailable == 0) ? (1 << XaddressWidth) : (1 << (XaddressWidth + 1));
parameter numberOfWordsPerRow = 1 << YaddressWidth;
parameter numberOfColumns = numberOfWordsPerRow * dataWidth;
parameter words = 1 << addressWidth;
parameter bits = words * dataWidth;
parameter XYaddressWidth = XaddressWidth + YaddressWidth;
parameter tPP = 100000.0:100000.0:100000.0;
parameter tPR = 100.0:100.0:100.0;
parameter tWP = 100.0:100.0:200.0;
parameter tWS = 11.0:16.0:25.0;
parameter tSP = 100.0:100.0:200.0;
parameter tVPPS = 100.0:100.0:200.0;
parameter tVPPH = 20.0:20.0:20.0;
parameter tRP = 15.0:23.0:43.0;
parameter tRP_DIFF = 6.0:11.0:20.0;
parameter tRPR = 5.0:9.0:18.0;
parameter tRPR_DIFF = 4.0:6.0:13.0;
parameter tRR = 4.0:6.0:12.0;
parameter tRACC = 1.0:1.4:2.3;
parameter tVRRS = 3000.0:3000.0:3000.0;
parameter tVRRH = 50.0:50.0:50.0;
parameter tLOAD = 0.6:1.0:1.7;
parameter tSS = 4.0:6.0:11.0;
parameter tRP_MAX = 2000.0:2000.0:2000.0;
parameter tAS = 3.0:6.0:11.0;
parameter tAH = 1.0:1.0:2.0;
parameter tDS = 1.0:1.0:1.0;
parameter tDH = 1.0:1.0:2.0;
parameter tWH = 1.0:1.0:2.0;
parameter tSH = 1.0:1.0:1.0;
parameter tMRS = 5.0:6.0:10.0;
parameter tMRH = 4.0:5.0:9.0;
parameter tQACC = 0.2:0.3:0.4;
parameter tQH = 0.3:0.4:0.5;
parameter tES = 3000.0:3000.0:3000.0;
parameter tEH = 50.0:50.0:50.0;
parameter tpw_CK_posedge_SEL_EQ_1_AND_WE_EQ_1 = tPP + 0.001;
parameter tpw_CK_posedge_SEL_EQ_1_AND_WE_EQ_0_AND_DIFF_EQ_0_AND_ORED_EQ_0 = tRP + 0.001;
parameter tpw_CK_posedge_SEL_EQ_1_AND_WE_EQ_0_AND_DIFF_EQ_1_AND_ORED_EQ_0 = tRP_DIFF + 0.001;
parameter tpw_CK_posedge_SEL_EQ_1_AND_WE_EQ_0_AND_DIFF_EQ_0_AND_ORED_EQ_1 = tRPR + 0.001;
parameter tpw_CK_posedge_SEL_EQ_1_AND_WE_EQ_0_AND_DIFF_EQ_1_AND_ORED_EQ_1 = tRPR_DIFF + 0.001;
parameter tpw_CK_negedge_PGM_EQ_1 = tPR + 0.001;
parameter tpw_CK_negedge_PGM_EQ_0 = tRR + 0.001;
parameter tsetup_CK_SEL_posedge_posedge_WE_EQ_1 = tSP + 0.001;
parameter tsetup_CK_SEL_posedge_negedge_WE_EQ_1 = tSS + 0.001;
parameter tsetup_CK_SEL_posedge_posedge_WE_EQ_0 = tSS + 0.001;
parameter tsetup_CK_SEL_posedge_negedge_WE_EQ_0 = tSS + 0.001;
parameter thold_CK_SEL_posedge_noedge = tSH + 0.001;
parameter tsetup_CK_WE_posedge_posedge_SEL_EQ_1 = tWP + 0.001;
parameter tsetup_CK_WE_posedge_negedge_SEL_EQ_1 = tWS + 0.001;
parameter thold_CK_WE_posedge_noedge_SEL_EQ_1 = tWH + 0.001;
parameter tsetup_CK_A_posedge_noedge_SEL_EQ_1 = tAS + 0.001;
parameter thold_CK_A_posedge_noedge_SEL_EQ_1 = tAH + 0.001;
parameter tsetup_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1 = tDS + 0.001;
parameter thold_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1 = tDH + 0.001;
parameter tncsetup_CK_VPP_posedge_posedge = tVPPS + 0.001;
parameter tnchold_CK_VPP_posedge_posedge = tVPPH + 0.001;
parameter tncsetup_CK_VRR_posedge_posedge = tVRRS + 0.001;
parameter tnchold_CK_VRR_posedge_posedge = tVRRH + 0.001;
parameter tncsetup_CK_MR_posedge_noedge = tMRS + 0.001;
parameter tnchold_CK_MR_posedge_noedge = tMRH + 0.001;
parameter tpd_CK_Q_negedge_noedge = tRACC + 0.001;
parameter ttr_CK_Q_negedge_noedge = tLOAD + 0.001;
parameter tpd_OE_Q_posedge_noedge = tQACC + 0.001;
parameter tpd_OE_Q_negedge_noedge = tQH + 0.001;
parameter ttr_OE_Q_posedge_noedge = tLOAD + 0.001;
parameter ttr_OE_Q_negedge_noedge = tLOAD + 0.001;
parameter tncsetup_CK_EHV_posedge_noedge = tES + 0.001;
parameter tnchold_CK_EHV_posedge_noedge = tEH + 0.001;
parameter tncsetup_SEL_EHV_posedge_noedge = tES + 0.001;
parameter tnchold_SEL_EHV_posedge_noedge = tEH + 0.001;
parameter tncsetup_WE_EHV_posedge_noedge = tES + 0.001;
parameter tnchold_WE_EHV_posedge_noedge = tEH + 0.001;
parameter tncsetup_VPP_EHV_posedge_noedge = tES + 0.001;
parameter tnchold_VPP_EHV_posedge_noedge = tEH + 0.001;
parameter tpw_PGM = tPP;
parameter trecovery_PGM = tPR;
parameter tpw_RD = tRP;
parameter tpw_RD_DIFF = tRP_DIFF;
parameter trecovery_RD = tRR;
parameter MODE_READ_DIFF_BIT = 0;
parameter MODE_READ_ORED_BIT = 4;
parameter MODE_READ_VERF_BIT = 6;
parameter MODE_TEST_WL_BIT = 1;
parameter MODE_TEST_BL_BIT = 2;
parameter MODE_TEST_SAP_BIT = 3;
parameter MODE_TEST_SAN_BIT = 5;
parameter MODE_TEST_CC_BIT = 7;
reg SEL;
reg CK;
reg TOP;
reg [(XYaddressWidth-1):0] AXY;
reg WE;
reg [(dataWidth-1):0] D;
wire [(dataWidth-1):0] Q;
reg OE;
reg diff;
reg ored;
reg verify;
reg testSAP;
reg testSAN;
reg testWL;
reg testBL;
reg testCC;
wire VPP;
wire VRR;
wire VREF;
reg EHV;
reg VPP_ENA;
reg VRR_ENA;
reg VREF_HIGH;
reg VREF_LOW;
bufif1(VPP, 1'b1, VPP_ENA);
bufif1(VRR, 1'b1, VRR_ENA);
bufif1(VREF, 1'b1, VREF_HIGH);
bufif1(VREF, 1'b0, VREF_LOW);
reg [(dataWidth-1):0] rom[0:(words-1)];
reg [(dataWidth-1):0] otp[0:(words-1)];
reg [(dataWidth-1):0] ref[0:(words-1)];
integer N;
integer testErrors;
reg lastRead;
wire [(XaddressWidth-1):0] rowAddress;
wire [(YaddressWidth-1):0] colAddress;
wire [(addressWidth-1):0] address;
assign colAddress = AXY >> XaddressWidth;
assign rowAddress = (XaddressWidth == 0) ? 0 : AXY;
assign address = (XaddressWidth == 0) ? {TOP, colAddress} : ((YaddressWidth == 0) ? {TOP, rowAddress} : {TOP, colAddress, rowAddress});
wire [(modeWidth-1):0] mode;
assign mode[MODE_READ_DIFF_BIT] = diff;
assign mode[MODE_READ_ORED_BIT] = ored;
assign mode[MODE_READ_VERF_BIT] = verify;
assign mode[MODE_TEST_WL_BIT] = testWL;
assign mode[MODE_TEST_BL_BIT] = testBL;
assign mode[MODE_TEST_SAP_BIT] = testSAP;
assign mode[MODE_TEST_SAN_BIT] = testSAN;
assign mode[MODE_TEST_CC_BIT] = testCC;
slp_b_tsmc180bcd50_4kx12_cm16d_ab_r20 dut(
   .A(address),
  .CK(CK),
  .D(D),
  .MR(mode),
  .OE(OE),
  .Q(Q),
  .SEL(SEL),
  .WE(WE),
  .VREF(VREF),
  .EHV(EHV),
  .VPP(VPP),
  .VRR(VRR)
);
initial begin
    VPP_ENA = 1'b0;
    VRR_ENA = 1'b1;
    VREF_HIGH = 1'b0;
    VREF_LOW = 1'b0;
    EHV = 1'b0;
    OE = 1'b1;
    diff = 1'b0;
    ored = 1'b0;
    verify = 1'b0;
    testSAP = 1'b0;
    testSAN = 1'b0;
    testWL = 1'b0;
    testBL = 1'b0;
    testCC = 1'b0;
    #(20.0) idle;
end
task idle;
begin
  CK = 1'b0;
  SEL = 1'bx;
  WE = 1'b0;
  TOP = 1'bx;
  AXY = {XYaddressWidth{1'bx}};
  D = {dataWidth{1'bx}};
  #(10.0);
end
endtask
task read;
input top;
input [(XYaddressWidth-1):0] addr;
real temp;
begin
  temp = (tsetup_CK_SEL_posedge_posedge_WE_EQ_0 > trecovery_RD) ? tsetup_CK_SEL_posedge_posedge_WE_EQ_0 : trecovery_RD;
  temp = (temp > tsetup_CK_A_posedge_noedge_SEL_EQ_1) ? temp : tsetup_CK_A_posedge_noedge_SEL_EQ_1 ;
  fork
    #(temp - tsetup_CK_SEL_posedge_posedge_WE_EQ_0) SEL = 1'b1;
    #(temp - tsetup_CK_A_posedge_noedge_SEL_EQ_1) {TOP, AXY} = {top, addr};
    #(temp);
  join
  CK = 1'b1;
  case({ored, diff})
    2'b00: temp = tpw_CK_posedge_SEL_EQ_1_AND_WE_EQ_0_AND_DIFF_EQ_0_AND_ORED_EQ_0;
    2'b01: temp = tpw_CK_posedge_SEL_EQ_1_AND_WE_EQ_0_AND_DIFF_EQ_1_AND_ORED_EQ_0;
    2'b10: temp = tpw_CK_posedge_SEL_EQ_1_AND_WE_EQ_0_AND_DIFF_EQ_0_AND_ORED_EQ_1;
    2'b11: temp = tpw_CK_posedge_SEL_EQ_1_AND_WE_EQ_0_AND_DIFF_EQ_1_AND_ORED_EQ_1;
  endcase
  fork
    #(thold_CK_SEL_posedge_noedge) SEL = 1'bx;
    #(thold_CK_A_posedge_noedge_SEL_EQ_1) {TOP, AXY} = {(XYaddressWidth + 1){1'bx}};
    #(temp);
  join
  CK = 1'b0;
  #(tpd_CK_Q_negedge_noedge) lastRead = 1'b1;
end
endtask
task write;
input top;
input [(XYaddressWidth-1):0] addr;
input [(dataWidth-1):0] data;
real temp;
begin
  SEL = 1'b1;
  WE = 1'b1;
  fork
    #(tsetup_CK_WE_posedge_posedge_SEL_EQ_1 - tsetup_CK_A_posedge_noedge_SEL_EQ_1) {TOP, AXY} = {top, addr};
    #(tsetup_CK_WE_posedge_posedge_SEL_EQ_1 - tsetup_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1) D = data;
    #(tsetup_CK_WE_posedge_posedge_SEL_EQ_1);
  join
  CK = 1'b1;
  fork
    #(thold_CK_SEL_posedge_noedge) SEL = 1'bx;
    #(thold_CK_WE_posedge_noedge_SEL_EQ_1) WE = 1'b0;
    #(thold_CK_A_posedge_noedge_SEL_EQ_1) {TOP, AXY} = {(XYaddressWidth + 1){1'bx}};
    #(thold_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1) D = {dataWidth{1'bx}};
    #(tpw_PGM);
  join
  CK = 1'b0;
  #(trecovery_PGM - trecovery_RD) lastRead = 1'b0;
end
endtask
task writeFirst;
input top;
input [(XYaddressWidth-1):0] addr;
input [(dataWidth-1):0] data;
real temp;
begin
  #(tnchold_CK_VPP_posedge_posedge);
  temp = tncsetup_CK_VPP_posedge_posedge;
  if (temp < tsetup_CK_WE_posedge_posedge_SEL_EQ_1) temp = tsetup_CK_WE_posedge_posedge_SEL_EQ_1;
  VPP_ENA = 1'b1;
  fork
    #(temp - tsetup_CK_SEL_posedge_posedge_WE_EQ_1) SEL = 1'b1;
    #(temp - tsetup_CK_WE_posedge_posedge_SEL_EQ_1) WE = 1'b1;
    #(temp - tsetup_CK_A_posedge_noedge_SEL_EQ_1) {TOP, AXY} = {top, addr};
    #(temp - tsetup_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1) D = data;
    #(temp);
  join
  CK = 1'b1;
  fork
    #(thold_CK_A_posedge_noedge_SEL_EQ_1) {TOP, AXY} = {(XYaddressWidth + 1){1'bx}};
    #(thold_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1) D = {dataWidth{1'bx}};
    #(tpw_PGM);
  join
  CK = 1'b0;
end
endtask
task writeNext;
input top;
input [(XYaddressWidth-1):0] addr;
input [(dataWidth-1):0] data;
real temp;
begin
  temp = trecovery_PGM;
  fork
    #(temp - tsetup_CK_A_posedge_noedge_SEL_EQ_1) {TOP, AXY} = {top, addr};
    #(temp - tsetup_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1) D = data;
    #(temp);
  join
  CK = 1'b1;
  fork
    #(thold_CK_A_posedge_noedge_SEL_EQ_1) {TOP, AXY} = {(XYaddressWidth + 1){1'bx}};
    #(thold_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1) D = {dataWidth{1'bx}};
    #(tpw_PGM);
  join
  CK = 1'b0;
end
endtask
task writeLast;
input top;
input [(XYaddressWidth-1):0] addr;
input [(dataWidth-1):0] data;
real temp;
begin
  temp = trecovery_PGM;
  fork
    #(temp - tsetup_CK_A_posedge_noedge_SEL_EQ_1) {TOP, AXY} = {top, addr};
    #(temp - tsetup_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1) D = data;
    #(temp);
  join
  CK = 1'b1;
  fork
    #(thold_CK_SEL_posedge_noedge) SEL = 1'bx;
    #(thold_CK_WE_posedge_noedge_SEL_EQ_1) WE = 1'b0;
    #(thold_CK_A_posedge_noedge_SEL_EQ_1) {TOP, AXY} = {(XYaddressWidth + 1){1'bx}};
    #(thold_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1) D = {dataWidth{1'bx}};
    #(tpw_PGM);
  join
  CK = 1'b0;
  fork
    #(tnchold_CK_VPP_posedge_posedge) VPP_ENA = 1'b0;
    #(trecovery_PGM - trecovery_RD);
  join
  lastRead = 1'b0;
end
endtask
task VppOn;
begin
  VPP_ENA = 1'b1;
  #(tncsetup_CK_VPP_posedge_posedge);
end
endtask
task VppOff;
begin
  #(tnchold_CK_VPP_posedge_posedge);
  VPP_ENA = 1'b0;
end
endtask
task programSequential;
input top;
input [(XYaddressWidth-1):0] addr;
input [(dataWidth-1):0] data;
input cntr;
input lastWord;
integer cntr;
reg [(dataWidth-1):0] temp;
integer i, j, k;
reg flag;
begin
  j = 0;
  temp = {dataWidth{1'b0}};
  for(i=0;i<dataWidth;i=i+1) begin
    if(data[i]) begin
      temp[i] = 1'b1;
      j = j + 1;
      if(j == cntr) begin
        if(VPP !== 1'b1) writeFirst(top, addr, temp);
        else begin
          if(lastWord) begin
            if(i == (dataWidth-1)) writeLast(top, addr, temp); else begin
              flag = 1'b0;
              for(k=i+1;k<dataWidth;k=k+1) if(data[k]) flag = 1'b1;
              if(flag) writeNext(top, addr, temp); else writeLast(top, addr, temp);
            end
          end else writeNext(top, addr, temp);
        end
        temp = {dataWidth{1'b0}};
        j = 0;
      end
    end
  end
  if(temp != {dataWidth{1'b0}}) begin
    if(lastWord) writeLast(top, addr, temp);
    else begin
      if(VPP !== 1'b1) writeFirst(top, addr, temp);
      else writeNext(top, addr, temp);
    end
  end
  if(lastWord & WE) WE = 0;
end
endtask
task randomData;
output [(dataWidth-1):0] d;
integer i;
begin
  i = dataWidth;
  while(i > 0) begin
    d = {d, $random};
    i = i - 32;
  end
end
endtask
function [(dataWidth-1):0] readOtp;
input [(addressWidth-1):0] a;
reg [(dataWidth-1):0] d, r;
integer i;
begin
  d = otp[a];
  r = rom[a];
  for(i=0;i<dataWidth;i=i+1) if(r[i] !== 1'bx) d[i] = r[i];
  readOtp = d;
end
endfunction
function [(dataWidth-1):0] readOtpDiff;
input [(addressWidth-1):0] a;
reg [(addressWidth-1):0] aN, aP;
reg [(dataWidth-1):0] dN, dP, d;
integer i;
begin
  if(diffAvailable) begin
    d = {dataWidth{1'bx}};
    aP = a;
    aN = a;
    aP[diffAddressBit] = 1'b1;
    aN[diffAddressBit] = 1'b0;
    dP = readOtp(aP);
    dN = readOtp(aN);
    for(i=0;i<dataWidth;i=i+1) begin
           if((dP[i] === 1'b1) && (dN[i] === 1'b0)) d[i] = 1'b1;
      else if((dP[i] === 1'b0) && (dN[i] === 1'b1)) d[i] = 1'b0;
    end
  end else begin
    d = readOtp(a);
    for(i=0;i<dataWidth;i=i+1) if(d[i] === 1'b0) d[i] = 1'bx;
  end
  readOtpDiff = d;
end
endfunction
function [(dataWidth-1):0] readOtpOred;
input [(addressWidth-1):0] a;
reg [(addressWidth-1):0] a0, a1;
reg [(dataWidth-1):0] d0, d1, d;
integer i;
begin
  a0 = a;
  a1 = a;
  a0[oredAddressBit] = 1'b0;
  a1[oredAddressBit] = 1'b1;
  d0 = readOtp(a0);
  d1 = readOtp(a1);
  d = d0 | d1;
  readOtpOred = d;
end
endfunction
function [(dataWidth-1):0] readOtpDiffOred;
input [(addressWidth-1):0] a;
reg [(addressWidth-1):0] aN, aP;
reg [(dataWidth-1):0] dN, dP, d;
integer i;
begin
  if(diffAvailable) begin
    d = {dataWidth{1'bx}};
    aP = a;
    aN = a;
    aP[diffAddressBit] = 1'b1;
    aN[diffAddressBit] = 1'b0;
    dP = readOtpOred(aP);
    dN = readOtpOred(aN);
    for(i=0;i<dataWidth;i=i+1) begin
           if((dP[i] === 1'b1) && (dN[i] === 1'b0)) d[i] = 1'b1;
      else if((dP[i] === 1'b0) && (dN[i] === 1'b1)) d[i] = 1'b0;
    end
  end else begin
    d = readOtpOred(a);
    for(i=0;i<dataWidth;i=i+1) if(d[i] === 1'b0) d[i] = 1'bx;
  end
  readOtpDiffOred = d;
end
endfunction
task check;
input offset;
input size;
integer offset, size;
integer i, j, e;
reg top;
reg [(XYaddressWidth-1):0] addr;
begin
  $display("[%0t]: CHECK from %0d to %0d, MR %b", $time, offset, offset + size - 1, dut.MR);
  e = 0;
  for(i=0;i<size;i=i+1) begin
    j = i + offset;
    {top, addr} = j;
    if(diffAvailable == 0) top = 1'b1;
    read(top, addr);
    if(Q !== ref[j]) begin
      e = e + 1;
      $display("[%0t]: ERROR: at %0d\nexpected %b\n  actual %b", $time, j, ref[j], Q);
    end
  end
  if(e > 0) $display("[%0t]: CHECK: FAIL with %0d mismatches", $time, e); else $display("[%0t]: CHECK: PASS", $time);
  testErrors = testErrors + e;
  fork
    #(tpw_CK_negedge_PGM_EQ_0);
    #(tnchold_CK_MR_posedge_noedge);
  join
end
endtask
task checkN;
  check(0, N);
endtask
initial begin : test
reg testStop;
reg top;
reg [(XYaddressWidth-1):0] addr;
reg [(dataWidth-1):0] data;
integer i, j;
time timeStamp;
$timeformat(-6, 3, " us", 0);
  dut.info;
  $display("\nINITIAL REFERENCE OTP <- all zeros");
  for(i=0;i<words;i=i+1) otp[i] = {dataWidth{1'b0}};
  if(romContentFile != "") begin
    $display("INITIAL REFERENCE ROM <- %0s", romContentFile);
    $readmemh(romContentFile, rom);
  end else begin
    $display("INITIAL REFERENCE ROM <- all 'X'");
  end
  $display();
  wait(~(CK & SEL));
    #(1000.0) EHV = 1'b1;
  #(tES);
  repeat(10) idle;
  $display("[%0t]: INFO: high Z state ON", $time);
  OE = 1'b0;
  repeat(10) idle;
  $display("[%0t]: INFO: high Z state OFF", $time);
  OE = 1'b1;
    testStop = 0;
  testErrors = 0;
  N = words;
  $display("\n################## 3.1.1 Sense Amplifier Operation Test Mode 'P' ###############\n");
  $display("REFERENCE MEMORY <- all ones");
  for(i=0;i<words;i=i+1) ref[i] = {dataWidth{1'b1}};
  #(tnchold_CK_MR_posedge_noedge);
  testSAP = 1;
  #(tncsetup_CK_MR_posedge_noedge);
  checkN;
  #(tnchold_CK_MR_posedge_noedge);
  testSAP = 0;
  #(tncsetup_CK_MR_posedge_noedge);
if(testStop) $stop;
  $display("\n################## 3.1.2 Sense Amplifier Operation Test Mode 'N' ###############\n");
  $display("REFERENCE MEMORY <- all zeros");
  for(i=0;i<words;i=i+1) ref[i] = {dataWidth{1'b0}};
  #(tnchold_CK_MR_posedge_noedge);
  testSAN = 1;
  #(tncsetup_CK_MR_posedge_noedge);
  checkN;
  #(tnchold_CK_MR_posedge_noedge);
  testSAN = 0;
  #(tncsetup_CK_MR_posedge_noedge);
if(testStop) $stop;
  $display("\n################## 3.1.3 Wordline Continuity Test ###############");
  $display("\n--------------- 3.1.3.1 Single Ended Mode\n");
  $display("REFERENCE <- single ended content");
  for(i=0;i<words;i=i+1) ref[i] = readOtp(i);
  $display("REFERENCE <- MSB one");
  for(i=0;i<words;i=i+1) begin data = ref[i]; data[(dataWidth-1)] = 1'b1; ref[i] = data; end
  #(tnchold_CK_MR_posedge_noedge);
  testWL = 1;
  #(tncsetup_CK_MR_posedge_noedge);
  checkN;
  #(tnchold_CK_MR_posedge_noedge);
  testWL = 0;
  #(tncsetup_CK_MR_posedge_noedge);
if(testStop) $stop;
if(diffAvailable) begin
  $display("\n--------------- 3.1.3.2 Redundant Differential Mode\n");
  $display("REFERENCE <- differential ored content");
  for(i=0;i<words;i=i+1) ref[i] = readOtpDiffOred(i);
  $display("REFERENCE <- MSB 'X'");
  for(i=0;i<words;i=i+1) begin data = ref[i]; data[(dataWidth-1)] = 1'bx; ref[i] = data; end
  #(tnchold_CK_MR_posedge_noedge);
  diff = 1;
  ored = 1;
  testWL = 1;
  #(tncsetup_CK_MR_posedge_noedge);
  checkN;
  #(tnchold_CK_MR_posedge_noedge);
  testWL = 0;
  diff = 0;
  ored = 0;
  #(tncsetup_CK_MR_posedge_noedge);
if(testStop) $stop;
end
  $display("\n--------------- 3.1.3.3 Redundant Mode\n");
  $display("REFERENCE <- ored content");
  for(i=0;i<words;i=i+1) ref[i] = readOtpOred(i);
  $display("REFERENCE <- MSB one");
  for(i=0;i<words;i=i+1) begin data = ref[i]; data[(dataWidth-1)] = 1'b1; ref[i] = data; end
  #(tnchold_CK_MR_posedge_noedge);
  ored = 1;
  testWL = 1;
  #(tncsetup_CK_MR_posedge_noedge);
  checkN;
  #(tnchold_CK_MR_posedge_noedge);
  testWL = 0;
  ored = 0;
  #(tncsetup_CK_MR_posedge_noedge);
if(testStop) $stop;
if(diffAvailable) begin
  $display("\n--------------- 3.1.3.4 Differential Mode\n");
  $display("REFERENCE <- differential content");
  for(i=0;i<words;i=i+1) ref[i] = readOtpDiff(i);
  $display("REFERENCE <- MSB 'X'");
  for(i=0;i<words;i=i+1) begin data = ref[i]; data[(dataWidth-1)] = 1'bx; ref[i] = data; end
  #(tnchold_CK_MR_posedge_noedge);
  diff = 1;
  testWL = 1;
  #(tncsetup_CK_MR_posedge_noedge);
  checkN;
  #(tnchold_CK_MR_posedge_noedge);
  testWL = 0;
  diff = 0;
  #(tncsetup_CK_MR_posedge_noedge);
if(testStop) $stop;
end
  $display("\n################## 3.1.4 Bitline Continuity Test ###############\n");
  $display("REFERENCE <- all ones");
  for(i=0;i<words;i=i+1) ref[i] = {dataWidth{1'b1}};
  #(tnchold_CK_MR_posedge_noedge);
  testBL = 1;
  #(tncsetup_CK_MR_posedge_noedge);
  checkN;
  #(tnchold_CK_MR_posedge_noedge);
  testBL = 0;
  #(tncsetup_CK_MR_posedge_noedge);
if(testStop) $stop;
  $display("\n################## 3.2.1 Program Cell Stress ###############\n");
  ored = 1;
  SEL = 1'b1;
  WE = 1'b1;
  D = {dataWidth{1'b0}};
    fork
      #(tncsetup_CK_MR_posedge_noedge);
    #(tsetup_CK_SEL_posedge_posedge_WE_EQ_1);
    #(tsetup_CK_WE_posedge_posedge_SEL_EQ_1);
    #(tsetup_CK_D_posedge_noedge_SEL_EQ_1_AND_WE_EQ_1);
    join
    for (i=0;i<words/2;i=i+1) begin
      fork
        begin {TOP, AXY} = i << 1; #(tsetup_CK_A_posedge_noedge_SEL_EQ_1); end
        #(tpw_CK_negedge_PGM_EQ_1);
      join
    CK = 1'b1;
      #(tpw_CK_posedge_SEL_EQ_1_AND_WE_EQ_1) CK = 1'b0;
    end
    fork
      #(tpw_CK_negedge_PGM_EQ_1);
    #(tnchold_CK_MR_posedge_noedge) ored = 0;
    join
  SEL = 1'b0;
  WE = 1'b0;
    #(tsetup_CK_WE_posedge_negedge_SEL_EQ_1);
    #(tncsetup_CK_MR_posedge_noedge);
  $display("REFERENCE <- single ended content");
  for(i=0;i<words;i=i+1) ref[i] = readOtp(i);
  checkN;
if(testStop) $stop;
  $display("\n################## 3.2.2 Read Cell Stress ###############\n");
  ored = 1;
  if(diffAvailable) diff = 1;
    SEL = 1'b1;
    fork
    #(tncsetup_CK_MR_posedge_noedge);
    #(tsetup_CK_SEL_posedge_posedge_WE_EQ_0);
    join
    for (i=0;i<words/4;i=i+1) begin
      fork
        begin {TOP, AXY} = i << 1; #(tsetup_CK_A_posedge_noedge_SEL_EQ_1); end
        #(tpw_CK_negedge_PGM_EQ_0);
      join
      CK = 1'b1;
      #(10000.0) CK = 1'b0;
    end
    fork
      #(tpw_CK_negedge_PGM_EQ_0);
      #(thold_CK_SEL_posedge_noedge) SEL = 1'b0;
      #(tnchold_CK_MR_posedge_noedge) begin ored = 0; diff = 0; end
    join
    #(tncsetup_CK_MR_posedge_noedge);
    $display("REFERENCE <- single ended content");
    for(i=0;i<words;i=i+1) ref[i] = readOtp(i);
    checkN;
if(testStop) $stop;
  $display("\n################## 3.3 Array Clean Test ###############\n");
  $display("EXPECTED DATA <- single ended content");
  j = 0;
  SEL = 1'b1;
  #(tsetup_CK_SEL_posedge_posedge_WE_EQ_0);
  for (i=0;i<words;i=i+1) begin
    data = readOtp(i);
      fork
        begin {TOP, AXY} = i; #(tsetup_CK_A_posedge_noedge_SEL_EQ_1); end
        #(tpw_CK_negedge_PGM_EQ_0);
      join
    CK = 1'b1;
    #(tRP_MAX) CK = 1'b0;
    #(tpd_CK_Q_negedge_noedge) if(Q !== data) begin
      j = j + 1;
      $display("[%0t]: ERROR: at %0d\nexpected all zeros\n  actual %b", $time, i,Q);
    end
  end
  if (j == 0) $display("[%0t]: PASS", $time); else begin
    testErrors = testErrors + j;
    $display("[%0t]: FAIL with %0d error(s)", $time, j);
  end
    fork
      #(tpw_CK_negedge_PGM_EQ_0);
      #(thold_CK_SEL_posedge_noedge) SEL = 1'b0;
    join
if(testStop) $stop;
  $display("\n################## 3.4.1 Program ###############\n");
  $display("REFERENCE OTP <- random");
  for(i=0;i<words;i=i+1) begin randomData(data); otp[i] = data; end
    if (diffAvailable) begin
    $display("BOTTOM HALF OF REFERENCE OTP <- ~TOP ONE");
    for(i=0;i<words/2;i=i+1) otp[i] = ~otp[i + words/2];
    end
  $display("EVEN HALF OF REFERENCE OTP <- ODD ONE");
  for(i=0;i<words/2;i=i+1) otp[2*i] = otp[2*i + 1];
  for(i=0;i<words;i=i+1) begin
    data = otp[i];
    {top, addr} = i;
    programSequential(top, addr, data, 1, i == (N-1));
  end
if(testStop) $stop;
  $display("\n################## 3.4.2 Verify ###############\n");
  $display("REFERENCE <- single ended content");
  for(i=0;i<words;i=i+1) ref[i] = readOtp(i);
  checkN;
if(testStop) $stop;
  $display("\n################## BACKDOOR SAVE and CLEAN ###############\n");
  $display("SAVE CORE OTP -> otp.dat");
  dut.writeOtp("otp.dat");
  $display("SAVE CORE ROM -> rom.dat");
  dut.writeRom("rom.dat");
  $display("CLEAN CORE OTP");
  dut.cleanOtp();
  $display("CLEAN CORE ROM");
  dut.cleanRom();
  $display("CLEAN REFERENCE OTP");
  for(i=0;i<words;i=i+1) otp[i] = {dataWidth{1'b0}};
  $display("CLEAN REFERENCE ROM");
  for(i=0;i<words;i=i+1) rom[i] = {dataWidth{1'bx}};
  $display("REFERENCE <- all zeros (single ended content)");
  for(i=0;i<words;i=i+1) ref[i] = readOtp(i);
  checkN;
if(testStop) $stop;
  $display("\n################## BACKDOOR LOAD #########################\n");
  $display("LOAD CORE OTP <- otp.dat");
  dut.readOtp("otp.dat");
  $display("LOAD CORE ROM <- rom.dat");
  dut.readRom("rom.dat");
  $display("LOAD REFERENCE OTP <- otp.dat");
  $readmemh("otp.dat", otp);
  $display("LOAD REFERENCE ROM <- rom.dat");
  $readmemh("rom.dat", rom);
  $display("REFERENCE <- single ended content");
  for(i=0;i<words;i=i+1) ref[i] = readOtp(i);
  checkN;
if(testStop) $stop;
  $display("\n################## 3.4.5 Verify Mission Mode ###############\n");
  $display("\n--------------- 3.4.5.1 Redundant Mode\n");
  $display("REFERENCE <- ored content");
  for(i=0;i<words;i=i+1) ref[i] = readOtpOred(i);
  ored = 1;
  #(tncsetup_CK_MR_posedge_noedge);
  checkN;
  #(tnchold_CK_MR_posedge_noedge);
  ored = 0;
if(testStop) $stop;
if(diffAvailable) begin
  $display("\n--------------- 3.4.5.2 Differential Mode\n");
  $display("REFERENCE <- differential content");
  for(i=0;i<words;i=i+1) ref[i] = readOtpDiff(i);
  diff = 1;
  #(tncsetup_CK_MR_posedge_noedge);
  checkN;
  #(tnchold_CK_MR_posedge_noedge);
  diff = 0;
if(testStop) $stop;
  $display("\n--------------- 3.4.5.3 Redundant Differential Mode\n");
  $display("REFERENCE <- differential ored content");
  for(i=0;i<words;i=i+1) ref[i] = readOtpDiffOred(i);
  diff = 1;
  ored = 1;
  #(tncsetup_CK_MR_posedge_noedge);
  checkN;
  #(tnchold_CK_MR_posedge_noedge);
  diff = 0;
  ored = 0;
if(testStop) $stop;
end
  $display("\n################## 3.5.1 Sense Amplifier Offset Test (Single Ended Mode), external VREF high ###############\n");
  $display("REFERENCE MEMORY <- all ones");
  for(i=0;i<words;i=i+1) ref[i] = {dataWidth{1'b1}};
  #(tnchold_CK_MR_posedge_noedge);
  testSAP = 1;
  verify = 1;
  VREF_HIGH = 1;
  #(tncsetup_CK_MR_posedge_noedge);
  checkN;
  #(tnchold_CK_MR_posedge_noedge);
  VREF_HIGH = 0;
  testSAP = 0;
  verify = 0;
  #(tncsetup_CK_MR_posedge_noedge);
if(testStop) $stop;
  $display("\n################## 3.5.1 Sense Amplifier Offset Test (Single Ended Mode), external VREF low ###############\n");
  $display("REFERENCE MEMORY <- all zeros");
  for(i=0;i<words;i=i+1) ref[i] = {dataWidth{1'b0}};
  #(tnchold_CK_MR_posedge_noedge);
  testSAP = 1;
  verify = 1;
  VREF_LOW = 1;
  #(tncsetup_CK_MR_posedge_noedge);
  checkN;
  #(tnchold_CK_MR_posedge_noedge);
  VREF_LOW = 0;
  testSAP = 0;
  verify = 0;
  #(tncsetup_CK_MR_posedge_noedge);
if(testStop) $stop;
  $display("\n################## 3.5.2 Sense Amplifier Offset Test (Differential Mode), external VREF high ###############\n");
  $display("REFERENCE MEMORY <- all ones");
  for(i=0;i<words;i=i+1) ref[i] = {dataWidth{1'b1}};
  #(tnchold_CK_MR_posedge_noedge);
  testSAP = 1;
  verify = 1;
  diff = 1;
  VREF_HIGH = 1;
  #(tncsetup_CK_MR_posedge_noedge);
  checkN;
  #(tnchold_CK_MR_posedge_noedge);
  VREF_HIGH = 0;
  testSAP = 0;
  verify = 0;
  diff = 0;
  #(tncsetup_CK_MR_posedge_noedge);
if(testStop) $stop;
  $display("\n################## 3.5.2 Sense Amplifier Offset Test (Differential Mode), external VREF low (not negative) ###############\n");
  $display("REFERENCE MEMORY <- all 'X'");
  for(i=0;i<words;i=i+1) ref[i] = {dataWidth{1'bx}};
  #(tnchold_CK_MR_posedge_noedge);
  testSAP = 1;
  verify = 1;
  diff = 1;
  VREF_LOW = 1;
  #(tncsetup_CK_MR_posedge_noedge);
  checkN;
  #(tnchold_CK_MR_posedge_noedge);
  VREF_LOW = 0;
  testSAP = 0;
  verify = 0;
  diff = 0;
  #(tncsetup_CK_MR_posedge_noedge);
if(testStop) $stop;
  $display("\n################## 3.5.3 Programmed Cell Margin Test, external VREF high ###############\n");
  $display("REFERENCE MEMORY <- all zeros");
  for(i=0;i<words;i=i+1) ref[i] = {dataWidth{1'b0}};
  VREF_HIGH = 1;
  testSAN = 1;
  verify = 1;
  #(tncsetup_CK_MR_posedge_noedge);
  checkN;
  #(tnchold_CK_MR_posedge_noedge);
  testSAN = 0;
  verify = 0;
  VREF_HIGH = 0;
if(testStop) $stop;
  $display("\n################## 3.5.3 Programmed Cell Margin Test, external VREF low ###############\n");
  $display("REFERENCE <- single ended content");
  for(i=0;i<words;i=i+1) ref[i] = readOtp(i);
  VREF_LOW = 1;
  testSAN = 1;
  verify = 1;
  #(tncsetup_CK_MR_posedge_noedge);
  checkN;
  #(tnchold_CK_MR_posedge_noedge);
  testSAN = 0;
  verify = 0;
  VREF_LOW = 0;
  #(tncsetup_CK_MR_posedge_noedge);
  $display();
  if(testErrors > 0) $display("[%0t]: test FAIL with %0d error(s)", $time, testErrors); else $display("[%0t]: test PASS", $time);
  $display("\n##################  DONE  ################################\n");
  $stop;
end
endmodule
