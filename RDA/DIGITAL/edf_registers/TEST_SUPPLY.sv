/* ###   interfaces   ###################################################### */

// TMR_ANA_SUPPLY
interface TEST_SUPPLY_TMR_ANA_SUPPLY_if;
  logic[15:0] value;
  logic VRR_2_ATB;
  logic VBG_2_ATB;
  logic VDDD_2_ATB;
  logic IC5U_2_ATB;
  logic IBP10U_2_ATB;

  modport master (
    output value, VRR_2_ATB, VBG_2_ATB, VDDD_2_ATB, IC5U_2_ATB, IBP10U_2_ATB
  );

  modport slave (
    input value, VRR_2_ATB, VBG_2_ATB, VDDD_2_ATB, IC5U_2_ATB, IBP10U_2_ATB
  );

endinterface : TEST_SUPPLY_TMR_ANA_SUPPLY_if

// TMR_DIG_SUPPLY
interface TEST_SUPPLY_TMR_DIG_SUPPLY_if;
  logic[15:0] value;
  logic PREVENT_OVERTEMPERATURE_SWITCH_OFF;

  modport master (
    output value, PREVENT_OVERTEMPERATURE_SWITCH_OFF
  );

  modport slave (
    input value, PREVENT_OVERTEMPERATURE_SWITCH_OFF
  );

endinterface : TEST_SUPPLY_TMR_DIG_SUPPLY_if

// TMR_ANA_TEMP_SENSOR
interface TEST_SUPPLY_TMR_ANA_TEMP_SENSOR_if;
  logic[15:0] value;
  logic DISCONNECT_TS;
  logic TS_2_ATB;

  modport master (
    output value, DISCONNECT_TS, TS_2_ATB
  );

  modport slave (
    input value, DISCONNECT_TS, TS_2_ATB
  );

endinterface : TEST_SUPPLY_TMR_ANA_TEMP_SENSOR_if

// TMR_ANA_OTP
interface TEST_SUPPLY_TMR_ANA_OTP_if;
  logic[15:0] value;
  logic OTP_VRR_LOAD;
  logic OTP_VPP_LOAD;
  logic OTP_VPP;
  logic OTP_VRR;
  logic OTP_VREF;
  logic OTP_VBG;

  modport master (
    output value, OTP_VRR_LOAD, OTP_VPP_LOAD, OTP_VPP, OTP_VRR, OTP_VREF, OTP_VBG
  );

  modport slave (
    input value, OTP_VRR_LOAD, OTP_VPP_LOAD, OTP_VPP, OTP_VRR, OTP_VREF, OTP_VBG
  );

endinterface : TEST_SUPPLY_TMR_ANA_OTP_if



/*###   TMR_ANA_SUPPLY   ######################################################*/
module TEST_SUPPLY_TMR_ANA_SUPPLY #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   TEST_SUPPLY_TMR_ANA_SUPPLY_if.master TEST_SUPPLY_TMR_ANA_SUPPLY);

   // TMR_ANA_SUPPLY : VRR_2_ATB
   logic  VRR_2_ATB, VRR_2_ATB_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       VRR_2_ATB <= 1'b0;
     end
     else begin
       VRR_2_ATB <= VRR_2_ATB_nxt;
     end
   end

   always_comb begin
     VRR_2_ATB_nxt = VRR_2_ATB;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       VRR_2_ATB_nxt = data_in[4:4]; 
     end
   end

   assign TEST_SUPPLY_TMR_ANA_SUPPLY.VRR_2_ATB = VRR_2_ATB;

   // TMR_ANA_SUPPLY : VBG_2_ATB
   logic  VBG_2_ATB, VBG_2_ATB_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       VBG_2_ATB <= 1'b0;
     end
     else begin
       VBG_2_ATB <= VBG_2_ATB_nxt;
     end
   end

   always_comb begin
     VBG_2_ATB_nxt = VBG_2_ATB;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       VBG_2_ATB_nxt = data_in[3:3]; 
     end
   end

   assign TEST_SUPPLY_TMR_ANA_SUPPLY.VBG_2_ATB = VBG_2_ATB;

   // TMR_ANA_SUPPLY : VDDD_2_ATB
   logic  VDDD_2_ATB, VDDD_2_ATB_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       VDDD_2_ATB <= 1'b0;
     end
     else begin
       VDDD_2_ATB <= VDDD_2_ATB_nxt;
     end
   end

   always_comb begin
     VDDD_2_ATB_nxt = VDDD_2_ATB;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       VDDD_2_ATB_nxt = data_in[2:2]; 
     end
   end

   assign TEST_SUPPLY_TMR_ANA_SUPPLY.VDDD_2_ATB = VDDD_2_ATB;

   // TMR_ANA_SUPPLY : IC5U_2_ATB
   logic  IC5U_2_ATB, IC5U_2_ATB_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       IC5U_2_ATB <= 1'b0;
     end
     else begin
       IC5U_2_ATB <= IC5U_2_ATB_nxt;
     end
   end

   always_comb begin
     IC5U_2_ATB_nxt = IC5U_2_ATB;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       IC5U_2_ATB_nxt = data_in[1:1]; 
     end
   end

   assign TEST_SUPPLY_TMR_ANA_SUPPLY.IC5U_2_ATB = IC5U_2_ATB;

   // TMR_ANA_SUPPLY : IBP10U_2_ATB
   logic  IBP10U_2_ATB, IBP10U_2_ATB_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       IBP10U_2_ATB <= 1'b0;
     end
     else begin
       IBP10U_2_ATB <= IBP10U_2_ATB_nxt;
     end
   end

   always_comb begin
     IBP10U_2_ATB_nxt = IBP10U_2_ATB;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       IBP10U_2_ATB_nxt = data_in[0:0]; 
     end
   end

   assign TEST_SUPPLY_TMR_ANA_SUPPLY.IBP10U_2_ATB = IBP10U_2_ATB;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {11'd0, VRR_2_ATB, VBG_2_ATB, VDDD_2_ATB, IC5U_2_ATB, IBP10U_2_ATB} : '0;

   assign TEST_SUPPLY_TMR_ANA_SUPPLY.value = {11'd0, VRR_2_ATB, VBG_2_ATB, VDDD_2_ATB, IC5U_2_ATB, IBP10U_2_ATB};

endmodule : TEST_SUPPLY_TMR_ANA_SUPPLY

/*###   TMR_DIG_SUPPLY   ######################################################*/
module TEST_SUPPLY_TMR_DIG_SUPPLY #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   TEST_SUPPLY_TMR_DIG_SUPPLY_if.master TEST_SUPPLY_TMR_DIG_SUPPLY);

   // TMR_DIG_SUPPLY : PREVENT_OVERTEMPERATURE_SWITCH_OFF
   logic  PREVENT_OVERTEMPERATURE_SWITCH_OFF, PREVENT_OVERTEMPERATURE_SWITCH_OFF_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       PREVENT_OVERTEMPERATURE_SWITCH_OFF <= 1'b0;
     end
     else begin
       PREVENT_OVERTEMPERATURE_SWITCH_OFF <= PREVENT_OVERTEMPERATURE_SWITCH_OFF_nxt;
     end
   end

   always_comb begin
     PREVENT_OVERTEMPERATURE_SWITCH_OFF_nxt = PREVENT_OVERTEMPERATURE_SWITCH_OFF;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       PREVENT_OVERTEMPERATURE_SWITCH_OFF_nxt = data_in[0:0]; 
     end
   end

   assign TEST_SUPPLY_TMR_DIG_SUPPLY.PREVENT_OVERTEMPERATURE_SWITCH_OFF = PREVENT_OVERTEMPERATURE_SWITCH_OFF;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {15'd0, PREVENT_OVERTEMPERATURE_SWITCH_OFF} : '0;

   assign TEST_SUPPLY_TMR_DIG_SUPPLY.value = {15'd0, PREVENT_OVERTEMPERATURE_SWITCH_OFF};

endmodule : TEST_SUPPLY_TMR_DIG_SUPPLY

/*###   TMR_ANA_TEMP_SENSOR   ######################################################*/
module TEST_SUPPLY_TMR_ANA_TEMP_SENSOR #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   TEST_SUPPLY_TMR_ANA_TEMP_SENSOR_if.master TEST_SUPPLY_TMR_ANA_TEMP_SENSOR);

   // TMR_ANA_TEMP_SENSOR : DISCONNECT_TS
   logic  DISCONNECT_TS, DISCONNECT_TS_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DISCONNECT_TS <= 1'b0;
     end
     else begin
       DISCONNECT_TS <= DISCONNECT_TS_nxt;
     end
   end

   always_comb begin
     DISCONNECT_TS_nxt = DISCONNECT_TS;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       DISCONNECT_TS_nxt = data_in[1:1]; 
     end
   end

   assign TEST_SUPPLY_TMR_ANA_TEMP_SENSOR.DISCONNECT_TS = DISCONNECT_TS;

   // TMR_ANA_TEMP_SENSOR : TS_2_ATB
   logic  TS_2_ATB, TS_2_ATB_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       TS_2_ATB <= 1'b0;
     end
     else begin
       TS_2_ATB <= TS_2_ATB_nxt;
     end
   end

   always_comb begin
     TS_2_ATB_nxt = TS_2_ATB;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       TS_2_ATB_nxt = data_in[0:0]; 
     end
   end

   assign TEST_SUPPLY_TMR_ANA_TEMP_SENSOR.TS_2_ATB = TS_2_ATB;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {14'd0, DISCONNECT_TS, TS_2_ATB} : '0;

   assign TEST_SUPPLY_TMR_ANA_TEMP_SENSOR.value = {14'd0, DISCONNECT_TS, TS_2_ATB};

endmodule : TEST_SUPPLY_TMR_ANA_TEMP_SENSOR

/*###   TMR_ANA_OTP   ######################################################*/
module TEST_SUPPLY_TMR_ANA_OTP #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   TEST_SUPPLY_TMR_ANA_OTP_if.master TEST_SUPPLY_TMR_ANA_OTP);

   // TMR_ANA_OTP : OTP_VRR_LOAD
   logic  OTP_VRR_LOAD, OTP_VRR_LOAD_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       OTP_VRR_LOAD <= 1'b0;
     end
     else begin
       OTP_VRR_LOAD <= OTP_VRR_LOAD_nxt;
     end
   end

   always_comb begin
     OTP_VRR_LOAD_nxt = OTP_VRR_LOAD;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       OTP_VRR_LOAD_nxt = data_in[5:5]; 
     end
   end

   assign TEST_SUPPLY_TMR_ANA_OTP.OTP_VRR_LOAD = OTP_VRR_LOAD;

   // TMR_ANA_OTP : OTP_VPP_LOAD
   logic  OTP_VPP_LOAD, OTP_VPP_LOAD_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       OTP_VPP_LOAD <= 1'b0;
     end
     else begin
       OTP_VPP_LOAD <= OTP_VPP_LOAD_nxt;
     end
   end

   always_comb begin
     OTP_VPP_LOAD_nxt = OTP_VPP_LOAD;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       OTP_VPP_LOAD_nxt = data_in[4:4]; 
     end
   end

   assign TEST_SUPPLY_TMR_ANA_OTP.OTP_VPP_LOAD = OTP_VPP_LOAD;

   // TMR_ANA_OTP : OTP_VPP
   logic  OTP_VPP, OTP_VPP_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       OTP_VPP <= 1'b0;
     end
     else begin
       OTP_VPP <= OTP_VPP_nxt;
     end
   end

   always_comb begin
     OTP_VPP_nxt = OTP_VPP;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       OTP_VPP_nxt = data_in[3:3]; 
     end
   end

   assign TEST_SUPPLY_TMR_ANA_OTP.OTP_VPP = OTP_VPP;

   // TMR_ANA_OTP : OTP_VRR
   logic  OTP_VRR, OTP_VRR_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       OTP_VRR <= 1'b0;
     end
     else begin
       OTP_VRR <= OTP_VRR_nxt;
     end
   end

   always_comb begin
     OTP_VRR_nxt = OTP_VRR;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       OTP_VRR_nxt = data_in[2:2]; 
     end
   end

   assign TEST_SUPPLY_TMR_ANA_OTP.OTP_VRR = OTP_VRR;

   // TMR_ANA_OTP : OTP_VREF
   logic  OTP_VREF, OTP_VREF_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       OTP_VREF <= 1'b0;
     end
     else begin
       OTP_VREF <= OTP_VREF_nxt;
     end
   end

   always_comb begin
     OTP_VREF_nxt = OTP_VREF;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       OTP_VREF_nxt = data_in[1:1]; 
     end
   end

   assign TEST_SUPPLY_TMR_ANA_OTP.OTP_VREF = OTP_VREF;

   // TMR_ANA_OTP : OTP_VBG
   logic  OTP_VBG, OTP_VBG_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       OTP_VBG <= 1'b0;
     end
     else begin
       OTP_VBG <= OTP_VBG_nxt;
     end
   end

   always_comb begin
     OTP_VBG_nxt = OTP_VBG;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       OTP_VBG_nxt = data_in[0:0]; 
     end
   end

   assign TEST_SUPPLY_TMR_ANA_OTP.OTP_VBG = OTP_VBG;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {10'd0, OTP_VRR_LOAD, OTP_VPP_LOAD, OTP_VPP, OTP_VRR, OTP_VREF, OTP_VBG} : '0;

   assign TEST_SUPPLY_TMR_ANA_OTP.value = {10'd0, OTP_VRR_LOAD, OTP_VPP_LOAD, OTP_VPP, OTP_VRR, OTP_VREF, OTP_VBG};

endmodule : TEST_SUPPLY_TMR_ANA_OTP

/*###   Registers   ######################################################*/
module TEST_SUPPLY #(
       parameter base_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   // register interfaces
   TEST_SUPPLY_TMR_ANA_SUPPLY_if.master TEST_SUPPLY_TMR_ANA_SUPPLY,
   TEST_SUPPLY_TMR_DIG_SUPPLY_if.master TEST_SUPPLY_TMR_DIG_SUPPLY,
   TEST_SUPPLY_TMR_ANA_TEMP_SENSOR_if.master TEST_SUPPLY_TMR_ANA_TEMP_SENSOR,
   TEST_SUPPLY_TMR_ANA_OTP_if.master TEST_SUPPLY_TMR_ANA_OTP
);

   logic[15:0] data_out_TMR_ANA_SUPPLY, data_out_TMR_DIG_SUPPLY, data_out_TMR_ANA_TEMP_SENSOR, data_out_TMR_ANA_OTP;

   TEST_SUPPLY_TMR_ANA_SUPPLY #( .reg_addr (base_addr + 'h0), .addr_width(addr_width) ) i_TEST_SUPPLY_TMR_ANA_SUPPLY ( .data_out (data_out_TMR_ANA_SUPPLY), .*);
   TEST_SUPPLY_TMR_DIG_SUPPLY #( .reg_addr (base_addr + 'h1), .addr_width(addr_width) ) i_TEST_SUPPLY_TMR_DIG_SUPPLY ( .data_out (data_out_TMR_DIG_SUPPLY), .*);
   TEST_SUPPLY_TMR_ANA_TEMP_SENSOR #( .reg_addr (base_addr + 'h4), .addr_width(addr_width) ) i_TEST_SUPPLY_TMR_ANA_TEMP_SENSOR ( .data_out (data_out_TMR_ANA_TEMP_SENSOR), .*);
   TEST_SUPPLY_TMR_ANA_OTP #( .reg_addr (base_addr + 'h5), .addr_width(addr_width) ) i_TEST_SUPPLY_TMR_ANA_OTP ( .data_out (data_out_TMR_ANA_OTP), .*);

   // output data assignment
   assign data_out = data_out_TMR_ANA_SUPPLY | data_out_TMR_DIG_SUPPLY | data_out_TMR_ANA_TEMP_SENSOR | data_out_TMR_ANA_OTP;

endmodule : TEST_SUPPLY
