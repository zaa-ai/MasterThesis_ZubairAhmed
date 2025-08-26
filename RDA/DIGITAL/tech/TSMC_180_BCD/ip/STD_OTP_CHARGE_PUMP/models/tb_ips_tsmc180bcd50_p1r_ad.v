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

`timescale 1ns/1ps

module tb_ips_tsmc180bcd50_p1r_ad;

event errorFlag;

parameter NMC = 64;
reg [ 8*NMC :0] tc_msg;
reg [ 8*NMC :0] ipsOutName;

reg [7:0] totalErrorCounter = 0;
reg [7:0] testErrorCounter = 0;

parameter tVPP_WARMUP = 300.0:600.0:1600.0;
parameter tVPP_SETUP  = 1000.0:1000.0:1000.0;
parameter tVRR_WARMUP = 2900.0:3900.0:6800.0;
parameter tVRR_SETUP  = 400.0:1700.0:4500.0;
parameter tVBG_WARMUP = 1600.0:3000.0:5700.0;

supply1 VDD;
supply1 VCC;
supply0 VSS;

reg CLKINSEL;
reg CLKIN;
reg VPPEN;
wire [7:0] MPP;
wire VPPPAD;

reg VRREN;
wire [15:0] MRR;

wire CLKOUT;
wire VPP;
wire VBG;
wire VREF;
wire VRR;
wire PPCLKOUT;

// MPP layout
reg [1:0] VppLevel;
reg VppLimitDis;
reg VppReferenceSelector;
reg [3:0] VppContolReserved;

assign MPP[1:0] = VppLevel;
assign MPP[2] = VppLimitDis;
assign MPP[3] = VppReferenceSelector;
assign MPP[7:4] = VppContolReserved;

// MRR layout
reg [3:0] VrrLevel;
reg [2:0] VrefLevel;
reg [1:0] VrrOutSel;
reg VbgOutputEnable;
reg VbgBiasDisable;
reg VbgPowerDown;
reg VrrPowerDown;
reg VrefOutputEnable;
reg VppOscillatorEnable;
reg VppOscillatorReducedFrequency;

assign MRR[3:0] = VrrLevel;
assign MRR[6:4] = VrefLevel;
assign MRR[7] = VrrOutSel[0];
assign MRR[8] = VbgOutputEnable;
assign MRR[9] = VbgBiasDisable;
assign MRR[10] = VbgPowerDown;
assign MRR[11] = VrrPowerDown;
assign MRR[12] = VrefOutputEnable;
assign MRR[13] = VppOscillatorEnable;
assign MRR[14] = VppOscillatorReducedFrequency;
assign MRR[15] = VrrOutSel[1];

ips_tsmc180bcd50_p1r_ad dut(
`ifdef HAVE_PG_PINS
   .VDD(VDD),
   .VSS(VSS),
   .VCC(VCC),
`endif
  .CLKINSEL(CLKINSEL),
  .CLKIN(CLKIN),
  .VPPEN(VPPEN),
  .MPP(MPP),
  .VPPPAD(VPPPAD),

  .VRREN(VRREN),
  .MRR(MRR),

  .CLKOUT(CLKOUT),
  .VPP(VPP),
  .VBG(VBG),
  .VREF(VREF),
  .VRR(VRR),
  .PPCLKOUT(PPCLKOUT)
);

reg ExtVppNode;
reg ExtVppEna;
reg ExtVbgEna;

bufif1 vpp_ext(VPPPAD, 1'b1, ExtVppEna);
bufif1 VBG_BUF(VBG, 1'b1, ExtVbgEna);

parameter tpw_CLKIN_posedge = 25.0;
parameter tpw_CLKIN_negedge = 25.0;
reg ExtClkEna;

initial begin : init

  #(tpw_CLKIN_posedge) ExtClkEna = 'b0;
  forever begin
    #(tpw_CLKIN_negedge) CLKIN = ExtClkEna;
    #(tpw_CLKIN_posedge) CLKIN = ExtClkEna ? 1'b0 : ExtClkEna;
  end
end


task CheckIpsOut;
   input  IpsOut;
   input  expIpsOut;
begin
  if (IpsOut !== expIpsOut  ) begin
    testErrorCounter = testErrorCounter + 1;
    $display("\n[%0t]  ERROR : ",$realtime, "  %0s",  ipsOutName, " = %b", IpsOut,  "  Expected %0s", ipsOutName," = %b \n", expIpsOut);
    -> errorFlag;
    //$stop;
  end else begin
    $display(" OK");
  end
end
endtask // CheckIpsOut

task testErrorStatistics;
begin
   if (testErrorCounter == 0) begin
     $display("[%0t] PASS: %0s PASSED",$realtime, tc_msg);
   end
   else begin
     $display("[%0t] FAIL: %0s FAILED  %0d",$realtime, tc_msg, testErrorCounter, "  times");
   end
   totalErrorCounter = totalErrorCounter + testErrorCounter;
   testErrorCounter = 0;
end
endtask // testErrorStatistics

task finaErrorStatistics;
begin
   if (totalErrorCounter == 0) begin
     $display("\n\n[%0t] PASS: IPS TEST PASSED",$realtime);
   end
   else begin
     $display("\n\n[%0t] FAIL: IPS TEST FAILED  %0d",$realtime, totalErrorCounter, "  times");
   end
end
endtask // finalERRORstatistics

task init_Ips;
begin
  VppLevel = 'b0;
  VppLimitDis = 'b0;
  VppReferenceSelector = 'b0;
  VppContolReserved = 'b0;

  VppOscillatorEnable = 'b0;
  VppOscillatorReducedFrequency = 'b0;

  VrrLevel = 'b0;
  VrrPowerDown = 'b0;

  VrefLevel = 'b0;
  VrefOutputEnable = 'b0;

  VrrOutSel = 2'b00;
  VbgBiasDisable = 'b0;
  VbgOutputEnable = 'b0;
  VbgPowerDown = 'b0;

  ExtVppEna = 'b0;
  ExtVbgEna = 'b0;
  VPPEN = 'b0;
  VRREN = 'b0;

  CLKINSEL = 'b0;
end
endtask

task do_clkTest;
begin
  $display("\n\n\n[%0t] INFO: CLOCK TEST \n", $time);
  tc_msg  = "CLOCK TEST";
  #(2000.0);
  ExtClkEna = 1;
  #(2000.0);
  CLKINSEL = 1;
  #(2000.0);
  ExtClkEna = 0;
  #(2000.0);
  VppOscillatorEnable = 1;
  #(2000.0);
  CLKINSEL = 0;
  #(2000.0);
  VppOscillatorReducedFrequency = 'b1;
  #(2000.0);
  VppOscillatorReducedFrequency = 'b0;
  #(2000.0);
  VppOscillatorEnable = 0;
  #(2000.0);
end
endtask

task do_vppTest;
begin
  tc_msg  = "VPP TEST";
  ipsOutName = "VPP";
  $display("\n\n\n[%0t] INFO: VPP TEST \n", $time);
  {VPPEN, VRREN, VbgPowerDown, VbgBiasDisable, VbgOutputEnable } = 5'b0_1_0_0_1;
  #(tVRR_WARMUP);
      //      MPP[3]               MPP[2]          MPP[1:0]
  $write("[%0t] INFO: Off or initial state: ", $time);
  {VPPEN, VppReferenceSelector, VppLimitDis, VppLevel,  ExtVppEna} = 6'b0_0_0_00_0;
  #(tVPP_WARMUP + 0.001) CheckIpsOut(VPP, 1'bz);

  $write("[%0t] INFO: Off state. External voltage applied to VPPPAD applied: ", $time);
  {VPPEN, VppReferenceSelector, VppLimitDis, VppLevel,  ExtVppEna} = 6'b0_0_0_00_1;
  #(tVPP_SETUP + 0.001) CheckIpsOut(VPP, 1'b1);

  $write("[%0t] INFO: Off or initial state: ", $time);
  {VPPEN, VppReferenceSelector, VppLimitDis, VppLevel,  ExtVppEna} = 6'b0_0_0_00_0;
  #(tVPP_WARMUP + 0.001) CheckIpsOut(VPP, 1'bz);

  $write("[%0t] INFO: Bandgap reference: ", $time);
  {VPPEN, VppReferenceSelector, VppLimitDis, VppLevel,  ExtVppEna} = 6'b1_0_0_00_0;
  #(tVPP_WARMUP + 0.001) CheckIpsOut(VPP, VCC);

  $write("[%0t] INFO: Bandgap default: ", $time);
  {VPPEN, VppReferenceSelector, VppLimitDis, VppLevel,  ExtVppEna} = 6'b1_0_0_01_0;
  #(tVPP_SETUP + 0.001) CheckIpsOut(VPP, 1'b1);

  $write("[%0t] INFO: Bandgap default: ", $time);
  {VPPEN, VppReferenceSelector, VppLimitDis, VppLevel,  ExtVppEna} = 6'b1_0_0_10_0;
  #(tVPP_SETUP + 0.001) CheckIpsOut(VPP, 1'b1);

  $write("[%0t] INFO: Bandgap default: ", $time);
  {VPPEN, VppReferenceSelector, VppLimitDis, VppLevel,  ExtVppEna} = 6'b1_0_0_11_0;
  #(tVPP_SETUP + 0.001) CheckIpsOut(VPP, 1'b1);

  $write("[%0t] INFO: VDD default: ", $time);
  {VPPEN, VppReferenceSelector, VppLimitDis, VppLevel,  ExtVppEna} = 6'b1_1_0_00_0;
  #(tVPP_SETUP + 0.001) CheckIpsOut(VPP, VDD);

  $write("[%0t] INFO: Free running pump. This mode is not allowed if pump is not loaded: ", $time);
  {VPPEN, VppReferenceSelector, VppLimitDis, VppLevel,  ExtVppEna} = 6'b1_0_1_11_0;
  #(tVPP_SETUP + 0.001) CheckIpsOut(VPP, 1'b1);

  $write("[%0t] INFO: VDD reference: ", $time);
  {VPPEN, VppReferenceSelector, VppLimitDis, VppLevel,  ExtVppEna} = 6'b1_1_0_11_0;
  #(tVPP_SETUP + 0.001) CheckIpsOut(VPP, VDD);
  testErrorStatistics;
end
endtask

task do_vrrTest;
begin
  tc_msg  = "VRR TEST";
  ipsOutName = "VRR";
  $display("\n\n\n[%0t] INFO: VRR TEST \n", $time);
    //    MRR[15,7]     MRR[11]       MRR[10]     MRR[9]       MRR[3:0]
  $write("[%0t] INFO: Off or initial state: ", $time);
  {VRREN, VrrOutSel, VrrPowerDown,VbgBiasDisable,VbgPowerDown, VrrLevel} = 10'b0_00_x_x_x_xxxx;
  #(tVRR_WARMUP + 0.001) CheckIpsOut(VRR, 1'bz);

  $write("[%0t] INFO: VRR diode mode: ", $time);
  {VRREN, VrrOutSel, VrrPowerDown,VbgBiasDisable,VbgPowerDown, VrrLevel} = 10'b0_01_x_x_x_xxxx;
  #(tVRR_WARMUP + 0.001) CheckIpsOut(VRR, VCC);

  $write("[%0t] INFO: VRR pulled to VCC: ", $time);
  {VRREN, VrrOutSel, VrrPowerDown,VbgBiasDisable,VbgPowerDown, VrrLevel} = 10'b0_10_x_x_x_xxxx;
  #(tVRR_WARMUP + 0.001) CheckIpsOut(VRR, VCC);

  $write("[%0t] INFO: VRR pulled to VDD: ", $time);
  {VRREN, VrrOutSel, VrrPowerDown,VbgBiasDisable,VbgPowerDown, VrrLevel} = 10'b0_11_x_x_x_0000;
  #(tVRR_WARMUP + 0.001) CheckIpsOut(VRR, VDD);

  $write("[%0t] INFO: VRR enabled. Default enable mode: ", $time);
  {VRREN, VrrOutSel, VrrPowerDown,VbgBiasDisable,VbgPowerDown, VrrLevel} = 10'b1_xx_0_0_0_0000;
  #(tVRR_WARMUP + 0.001) CheckIpsOut(VRR, 1'b1);

  $write("[%0t] INFO: VRR enable. Default enable mode: ", $time);
  {VRREN, VrrOutSel, VrrPowerDown,VbgBiasDisable,VbgPowerDown, VrrLevel} = 10'b1_xx_0_0_0_0001;
  #(tVRR_SETUP + 0.001) CheckIpsOut(VRR, 1'b1);

  $write("[%0t] INFO: VRR enable. Default enable mode: ", $time);
  {VRREN, VrrOutSel, VrrPowerDown,VbgBiasDisable,VbgPowerDown, VrrLevel} = 10'b1_xx_0_0_0_0101;
  #(tVRR_SETUP + 0.001) CheckIpsOut(VRR, 1'b1);

  $write("[%0t] INFO: Memory model test. VRR Power down mode. Bandgap disabled: ", $time);
  {VRREN, VrrOutSel, VrrPowerDown,VbgBiasDisable,VbgPowerDown, VrrLevel} = 10'b1_xx_1_0_0_0000;
  #(tVRR_WARMUP + 0.001) CheckIpsOut(VRR, 1'bx);

  $write("[%0t] INFO: Bandgap disabled mode: ", $time);
  {VRREN, VrrOutSel, VrrPowerDown,VbgBiasDisable,VbgPowerDown, VrrLevel} = 10'b1_xx_0_1_1_0110;
  #(tVRR_WARMUP + 0.001) CheckIpsOut(VRR, 1'bx);
  testErrorStatistics;
end
endtask

task do_vbgTest;
begin
  tc_msg  = "VBG TEST";
  ipsOutName = "VBG";
  $display("\n\n\n[%0t] INFO: VBG TEST \n", $time);
     //            MRR[10]       MRR[9]         MRR[8]
  $write("[%0t] INFO: Off or initial state: ", $time);
  {VPPEN, VRREN, VbgPowerDown, VbgBiasDisable, VbgOutputEnable } = 5'b0_0_x_x_0;
  #(tVBG_WARMUP + 0.001) CheckIpsOut(VBG, 1'bz);

  $write("[%0t] INFO: VBG on. VBG output enabled: ", $time);
  {VPPEN, VRREN, VbgPowerDown, VbgBiasDisable, VbgOutputEnable } = 5'bx_1_0_0_1;
  #(tVBG_WARMUP + 0.001) CheckIpsOut(VBG, 1'b1);

  $write("[%0t] INFO: VBG on. VBG output enabled (by VPPEN = 1): ", $time);
  {VPPEN, VRREN, VbgPowerDown, VbgBiasDisable, VbgOutputEnable } = 5'b1_1_0_0_x;
  #(tVBG_WARMUP + 0.001) CheckIpsOut(VBG, 1'b1);

  $write("[%0t] INFO: VBG Bias disabled. VBG output enabled: ", $time);
  {VPPEN, VRREN, VbgPowerDown, VbgBiasDisable, VbgOutputEnable } = 5'b1_1_0_1_1;
  #(tVBG_WARMUP + 0.001) CheckIpsOut(VBG, 1'bz);

  $write("[%0t] INFO: Memory model test. VBG Power down. VBG output enabled: ", $time);
  {VPPEN, VRREN, VbgPowerDown, VbgBiasDisable, VbgOutputEnable } = 5'bx_1_1_0_1;
  #(tVBG_WARMUP + 0.001) CheckIpsOut(VBG, 1'bx);

  $write("[%0t] INFO: VBG Power down. VBG Bias disabled. VBG output enabled: ", $time);
  {VPPEN, VRREN, VbgPowerDown, VbgBiasDisable, VbgOutputEnable } = 5'bx_1_1_1_1;
  #(tVBG_WARMUP + 0.001) CheckIpsOut(VBG, 1'bz);

  $write("[%0t] INFO: VBG output disabled: ", $time);
  {VPPEN, VRREN, VbgPowerDown, VbgBiasDisable, VbgOutputEnable } = 5'b0_0_x_x_0;
  #(tVBG_WARMUP + 0.001) CheckIpsOut(VBG, 1'bz);

  testErrorStatistics;
end
endtask

task do_vrefTest;
begin
  tc_msg  = "VREF TEST";
  ipsOutName = "VREF";
  $display("\n\n\n[%0t] INFO:  VREF TEST \n", $time);
  {VRREN, VrrOutSel, VrrPowerDown,VbgBiasDisable,VbgPowerDown, VrrLevel} = 10'b0_00_00_0_0000;
     //     MRR[12]          MRR[6:4]
  $write("[%0t] INFO: Off or initial state: ", $time);
  {VRREN, VrefOutputEnable, VrefLevel } = 5'b0_0_000;
  #(tVRR_WARMUP + 0.001) CheckIpsOut(VREF, 1'bz);

  $write("[%0t] INFO: Off or initial state. VREF output enabled: ", $time);
  {VRREN, VrefOutputEnable, VrefLevel } = 5'b0_1_000;
  #(tVRR_WARMUP + 0.001) CheckIpsOut(VREF, 1'bx);

  $write("[%0t] INFO: VREF enabled. VREF output disabled: ", $time);
  {VRREN, VrefOutputEnable, VrefLevel } = 5'b1_0_000;
  #(tVRR_WARMUP + 0.001) CheckIpsOut(VREF, 1'bz);

  $write("[%0t] INFO: VREF enabled. VREF output enabled: ", $time);
  {VRREN, VrefOutputEnable, VrefLevel } = 5'b1_1_000;
  #(tVRR_WARMUP + 0.001) CheckIpsOut(VREF, 1'b1);
  testErrorStatistics;
end
endtask


initial begin : test

  $timeformat(-6, 3, " us", 0);

  init_Ips;

  do_vbgTest;

  do_vrrTest;

  do_vrefTest;

  do_vppTest;

  do_clkTest;

  finaErrorStatistics;
  $stop;

end

endmodule // tb_ips_tsmc180bcd50_p1r_ad
