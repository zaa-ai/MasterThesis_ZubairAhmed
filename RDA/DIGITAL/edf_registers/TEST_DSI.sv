/* ###   interfaces   ###################################################### */

// TMR_ANA_DSI3_TX
interface TEST_DSI_TMR_ANA_DSI3_TX_if;
  logic[15:0] value;
  logic IDAC_TX_CH1_2;
  logic VBN5V_DIV_CH1_2;
  logic INP_CH1_2;
  logic INN_CH1_2;
  logic VNG0_CH1_2;
  logic VNC0_CH1_2;
  logic VNC2_CH1_2;

  modport master (
    output value, IDAC_TX_CH1_2, VBN5V_DIV_CH1_2, INP_CH1_2, INN_CH1_2, VNG0_CH1_2, VNC0_CH1_2, VNC2_CH1_2
  );

  modport slave (
    input value, IDAC_TX_CH1_2, VBN5V_DIV_CH1_2, INP_CH1_2, INN_CH1_2, VNG0_CH1_2, VNC0_CH1_2, VNC2_CH1_2
  );

endinterface : TEST_DSI_TMR_ANA_DSI3_TX_if

// TMR_ANA_DSI3_RX
interface TEST_DSI_TMR_ANA_DSI3_RX_if;
  logic[15:0] value;
  logic I_Q_2_ATB;

  modport master (
    output value, I_Q_2_ATB
  );

  modport slave (
    input value, I_Q_2_ATB
  );

endinterface : TEST_DSI_TMR_ANA_DSI3_RX_if

// TMR_DIG_DSI3
interface TEST_DSI_TMR_DIG_DSI3_if;
  logic[15:0] value;
  logic PREVENT_DEACTIVATION;

  modport master (
    output value, PREVENT_DEACTIVATION
  );

  modport slave (
    input value, PREVENT_DEACTIVATION
  );

endinterface : TEST_DSI_TMR_DIG_DSI3_if

// TMR_SEL_DSI3
interface TEST_DSI_TMR_SEL_DSI3_if;
  logic[15:0] value;
  logic RX_ON;
  logic HVCASC_ON;
  logic TX_ON;
  logic RX_TXN;
  logic TX;

  modport master (
    output value, RX_ON, HVCASC_ON, TX_ON, RX_TXN, TX
  );

  modport slave (
    input value, RX_ON, HVCASC_ON, TX_ON, RX_TXN, TX
  );

endinterface : TEST_DSI_TMR_SEL_DSI3_if

// TMR_VAL_DSI3
interface TEST_DSI_TMR_VAL_DSI3_if;
  logic[15:0] value;
  logic RX_ON;
  logic HVCASC_ON;
  logic TX_ON;
  logic RX_TXN;
  logic TX;

  modport master (
    output value, RX_ON, HVCASC_ON, TX_ON, RX_TXN, TX
  );

  modport slave (
    input value, RX_ON, HVCASC_ON, TX_ON, RX_TXN, TX
  );

endinterface : TEST_DSI_TMR_VAL_DSI3_if

// TMR_IN_DSI3
interface TEST_DSI_TMR_IN_DSI3_if;
  logic[15:0] value;
  logic[2:0] tmr_in_tx;

  modport master (
    output value, tmr_in_tx
  );

  modport slave (
    input value, tmr_in_tx
  );

endinterface : TEST_DSI_TMR_IN_DSI3_if



/*###   TMR_ANA_DSI3_TX   ######################################################*/
module TEST_DSI_TMR_ANA_DSI3_TX #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   TEST_DSI_TMR_ANA_DSI3_TX_if.master TEST_DSI_TMR_ANA_DSI3_TX);

   // TMR_ANA_DSI3_TX : IDAC_TX_CH1_2
   logic  IDAC_TX_CH1_2, IDAC_TX_CH1_2_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       IDAC_TX_CH1_2 <= 1'b0;
     end
     else begin
       IDAC_TX_CH1_2 <= IDAC_TX_CH1_2_nxt;
     end
   end

   always_comb begin
     IDAC_TX_CH1_2_nxt = IDAC_TX_CH1_2;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       IDAC_TX_CH1_2_nxt = data_in[6:6]; 
     end
   end

   assign TEST_DSI_TMR_ANA_DSI3_TX.IDAC_TX_CH1_2 = IDAC_TX_CH1_2;

   // TMR_ANA_DSI3_TX : VBN5V_DIV_CH1_2
   logic  VBN5V_DIV_CH1_2, VBN5V_DIV_CH1_2_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       VBN5V_DIV_CH1_2 <= 1'b0;
     end
     else begin
       VBN5V_DIV_CH1_2 <= VBN5V_DIV_CH1_2_nxt;
     end
   end

   always_comb begin
     VBN5V_DIV_CH1_2_nxt = VBN5V_DIV_CH1_2;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       VBN5V_DIV_CH1_2_nxt = data_in[5:5]; 
     end
   end

   assign TEST_DSI_TMR_ANA_DSI3_TX.VBN5V_DIV_CH1_2 = VBN5V_DIV_CH1_2;

   // TMR_ANA_DSI3_TX : INP_CH1_2
   logic  INP_CH1_2, INP_CH1_2_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       INP_CH1_2 <= 1'b0;
     end
     else begin
       INP_CH1_2 <= INP_CH1_2_nxt;
     end
   end

   always_comb begin
     INP_CH1_2_nxt = INP_CH1_2;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       INP_CH1_2_nxt = data_in[4:4]; 
     end
   end

   assign TEST_DSI_TMR_ANA_DSI3_TX.INP_CH1_2 = INP_CH1_2;

   // TMR_ANA_DSI3_TX : INN_CH1_2
   logic  INN_CH1_2, INN_CH1_2_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       INN_CH1_2 <= 1'b0;
     end
     else begin
       INN_CH1_2 <= INN_CH1_2_nxt;
     end
   end

   always_comb begin
     INN_CH1_2_nxt = INN_CH1_2;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       INN_CH1_2_nxt = data_in[3:3]; 
     end
   end

   assign TEST_DSI_TMR_ANA_DSI3_TX.INN_CH1_2 = INN_CH1_2;

   // TMR_ANA_DSI3_TX : VNG0_CH1_2
   logic  VNG0_CH1_2, VNG0_CH1_2_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       VNG0_CH1_2 <= 1'b0;
     end
     else begin
       VNG0_CH1_2 <= VNG0_CH1_2_nxt;
     end
   end

   always_comb begin
     VNG0_CH1_2_nxt = VNG0_CH1_2;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       VNG0_CH1_2_nxt = data_in[2:2]; 
     end
   end

   assign TEST_DSI_TMR_ANA_DSI3_TX.VNG0_CH1_2 = VNG0_CH1_2;

   // TMR_ANA_DSI3_TX : VNC0_CH1_2
   logic  VNC0_CH1_2, VNC0_CH1_2_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       VNC0_CH1_2 <= 1'b0;
     end
     else begin
       VNC0_CH1_2 <= VNC0_CH1_2_nxt;
     end
   end

   always_comb begin
     VNC0_CH1_2_nxt = VNC0_CH1_2;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       VNC0_CH1_2_nxt = data_in[1:1]; 
     end
   end

   assign TEST_DSI_TMR_ANA_DSI3_TX.VNC0_CH1_2 = VNC0_CH1_2;

   // TMR_ANA_DSI3_TX : VNC2_CH1_2
   logic  VNC2_CH1_2, VNC2_CH1_2_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       VNC2_CH1_2 <= 1'b0;
     end
     else begin
       VNC2_CH1_2 <= VNC2_CH1_2_nxt;
     end
   end

   always_comb begin
     VNC2_CH1_2_nxt = VNC2_CH1_2;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       VNC2_CH1_2_nxt = data_in[0:0]; 
     end
   end

   assign TEST_DSI_TMR_ANA_DSI3_TX.VNC2_CH1_2 = VNC2_CH1_2;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {9'd0, IDAC_TX_CH1_2, VBN5V_DIV_CH1_2, INP_CH1_2, INN_CH1_2, VNG0_CH1_2, VNC0_CH1_2, VNC2_CH1_2} : '0;

   assign TEST_DSI_TMR_ANA_DSI3_TX.value = {9'd0, IDAC_TX_CH1_2, VBN5V_DIV_CH1_2, INP_CH1_2, INN_CH1_2, VNG0_CH1_2, VNC0_CH1_2, VNC2_CH1_2};

endmodule : TEST_DSI_TMR_ANA_DSI3_TX

/*###   TMR_ANA_DSI3_RX   ######################################################*/
module TEST_DSI_TMR_ANA_DSI3_RX #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   TEST_DSI_TMR_ANA_DSI3_RX_if.master TEST_DSI_TMR_ANA_DSI3_RX);

   // TMR_ANA_DSI3_RX : I_Q_2_ATB
   logic  I_Q_2_ATB, I_Q_2_ATB_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       I_Q_2_ATB <= 1'b0;
     end
     else begin
       I_Q_2_ATB <= I_Q_2_ATB_nxt;
     end
   end

   always_comb begin
     I_Q_2_ATB_nxt = I_Q_2_ATB;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       I_Q_2_ATB_nxt = data_in[0:0]; 
     end
   end

   assign TEST_DSI_TMR_ANA_DSI3_RX.I_Q_2_ATB = I_Q_2_ATB;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {15'd0, I_Q_2_ATB} : '0;

   assign TEST_DSI_TMR_ANA_DSI3_RX.value = {15'd0, I_Q_2_ATB};

endmodule : TEST_DSI_TMR_ANA_DSI3_RX

/*###   TMR_DIG_DSI3   ######################################################*/
module TEST_DSI_TMR_DIG_DSI3 #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   TEST_DSI_TMR_DIG_DSI3_if.master TEST_DSI_TMR_DIG_DSI3);

   // TMR_DIG_DSI3 : PREVENT_DEACTIVATION
   logic  PREVENT_DEACTIVATION, PREVENT_DEACTIVATION_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       PREVENT_DEACTIVATION <= 1'b0;
     end
     else begin
       PREVENT_DEACTIVATION <= PREVENT_DEACTIVATION_nxt;
     end
   end

   always_comb begin
     PREVENT_DEACTIVATION_nxt = PREVENT_DEACTIVATION;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       PREVENT_DEACTIVATION_nxt = data_in[0:0]; 
     end
   end

   assign TEST_DSI_TMR_DIG_DSI3.PREVENT_DEACTIVATION = PREVENT_DEACTIVATION;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {15'd0, PREVENT_DEACTIVATION} : '0;

   assign TEST_DSI_TMR_DIG_DSI3.value = {15'd0, PREVENT_DEACTIVATION};

endmodule : TEST_DSI_TMR_DIG_DSI3

/*###   TMR_SEL_DSI3   ######################################################*/
module TEST_DSI_TMR_SEL_DSI3 #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   TEST_DSI_TMR_SEL_DSI3_if.master TEST_DSI_TMR_SEL_DSI3);

   // TMR_SEL_DSI3 : RX_ON
   logic  RX_ON, RX_ON_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       RX_ON <= 1'b0;
     end
     else begin
       RX_ON <= RX_ON_nxt;
     end
   end

   always_comb begin
     RX_ON_nxt = RX_ON;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       RX_ON_nxt = data_in[4:4]; 
     end
   end

   assign TEST_DSI_TMR_SEL_DSI3.RX_ON = RX_ON;

   // TMR_SEL_DSI3 : HVCASC_ON
   logic  HVCASC_ON, HVCASC_ON_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       HVCASC_ON <= 1'b0;
     end
     else begin
       HVCASC_ON <= HVCASC_ON_nxt;
     end
   end

   always_comb begin
     HVCASC_ON_nxt = HVCASC_ON;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       HVCASC_ON_nxt = data_in[3:3]; 
     end
   end

   assign TEST_DSI_TMR_SEL_DSI3.HVCASC_ON = HVCASC_ON;

   // TMR_SEL_DSI3 : TX_ON
   logic  TX_ON, TX_ON_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       TX_ON <= 1'b0;
     end
     else begin
       TX_ON <= TX_ON_nxt;
     end
   end

   always_comb begin
     TX_ON_nxt = TX_ON;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       TX_ON_nxt = data_in[2:2]; 
     end
   end

   assign TEST_DSI_TMR_SEL_DSI3.TX_ON = TX_ON;

   // TMR_SEL_DSI3 : RX_TXN
   logic  RX_TXN, RX_TXN_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       RX_TXN <= 1'b0;
     end
     else begin
       RX_TXN <= RX_TXN_nxt;
     end
   end

   always_comb begin
     RX_TXN_nxt = RX_TXN;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       RX_TXN_nxt = data_in[1:1]; 
     end
   end

   assign TEST_DSI_TMR_SEL_DSI3.RX_TXN = RX_TXN;

   // TMR_SEL_DSI3 : TX
   logic  TX, TX_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       TX <= 1'b0;
     end
     else begin
       TX <= TX_nxt;
     end
   end

   always_comb begin
     TX_nxt = TX;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       TX_nxt = data_in[0:0]; 
     end
   end

   assign TEST_DSI_TMR_SEL_DSI3.TX = TX;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {11'd0, RX_ON, HVCASC_ON, TX_ON, RX_TXN, TX} : '0;

   assign TEST_DSI_TMR_SEL_DSI3.value = {11'd0, RX_ON, HVCASC_ON, TX_ON, RX_TXN, TX};

endmodule : TEST_DSI_TMR_SEL_DSI3

/*###   TMR_VAL_DSI3   ######################################################*/
module TEST_DSI_TMR_VAL_DSI3 #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   TEST_DSI_TMR_VAL_DSI3_if.master TEST_DSI_TMR_VAL_DSI3);

   // TMR_VAL_DSI3 : RX_ON
   logic  RX_ON, RX_ON_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       RX_ON <= 1'b0;
     end
     else begin
       RX_ON <= RX_ON_nxt;
     end
   end

   always_comb begin
     RX_ON_nxt = RX_ON;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       RX_ON_nxt = data_in[4:4]; 
     end
   end

   assign TEST_DSI_TMR_VAL_DSI3.RX_ON = RX_ON;

   // TMR_VAL_DSI3 : HVCASC_ON
   logic  HVCASC_ON, HVCASC_ON_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       HVCASC_ON <= 1'b0;
     end
     else begin
       HVCASC_ON <= HVCASC_ON_nxt;
     end
   end

   always_comb begin
     HVCASC_ON_nxt = HVCASC_ON;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       HVCASC_ON_nxt = data_in[3:3]; 
     end
   end

   assign TEST_DSI_TMR_VAL_DSI3.HVCASC_ON = HVCASC_ON;

   // TMR_VAL_DSI3 : TX_ON
   logic  TX_ON, TX_ON_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       TX_ON <= 1'b0;
     end
     else begin
       TX_ON <= TX_ON_nxt;
     end
   end

   always_comb begin
     TX_ON_nxt = TX_ON;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       TX_ON_nxt = data_in[2:2]; 
     end
   end

   assign TEST_DSI_TMR_VAL_DSI3.TX_ON = TX_ON;

   // TMR_VAL_DSI3 : RX_TXN
   logic  RX_TXN, RX_TXN_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       RX_TXN <= 1'b0;
     end
     else begin
       RX_TXN <= RX_TXN_nxt;
     end
   end

   always_comb begin
     RX_TXN_nxt = RX_TXN;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       RX_TXN_nxt = data_in[1:1]; 
     end
   end

   assign TEST_DSI_TMR_VAL_DSI3.RX_TXN = RX_TXN;

   // TMR_VAL_DSI3 : TX
   logic  TX, TX_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       TX <= 1'b0;
     end
     else begin
       TX <= TX_nxt;
     end
   end

   always_comb begin
     TX_nxt = TX;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       TX_nxt = data_in[0:0]; 
     end
   end

   assign TEST_DSI_TMR_VAL_DSI3.TX = TX;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {11'd0, RX_ON, HVCASC_ON, TX_ON, RX_TXN, TX} : '0;

   assign TEST_DSI_TMR_VAL_DSI3.value = {11'd0, RX_ON, HVCASC_ON, TX_ON, RX_TXN, TX};

endmodule : TEST_DSI_TMR_VAL_DSI3

/*###   TMR_IN_DSI3   ######################################################*/
module TEST_DSI_TMR_IN_DSI3 #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   TEST_DSI_TMR_IN_DSI3_if.master TEST_DSI_TMR_IN_DSI3);

   // TMR_IN_DSI3 : tmr_in_tx
   logic[2:0]  tmr_in_tx, tmr_in_tx_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       tmr_in_tx <= 3'b0;
     end
     else begin
       tmr_in_tx <= tmr_in_tx_nxt;
     end
   end

   always_comb begin
     tmr_in_tx_nxt = tmr_in_tx;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       tmr_in_tx_nxt = data_in[2:0]; 
     end
   end

   assign TEST_DSI_TMR_IN_DSI3.tmr_in_tx = tmr_in_tx;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {13'd0, tmr_in_tx} : '0;

   assign TEST_DSI_TMR_IN_DSI3.value = {13'd0, tmr_in_tx};

endmodule : TEST_DSI_TMR_IN_DSI3

/*###   Registers   ######################################################*/
module TEST_DSI #(
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
   TEST_DSI_TMR_ANA_DSI3_TX_if.master TEST_DSI_TMR_ANA_DSI3_TX,
   TEST_DSI_TMR_ANA_DSI3_RX_if.master TEST_DSI_TMR_ANA_DSI3_RX,
   TEST_DSI_TMR_DIG_DSI3_if.master TEST_DSI_TMR_DIG_DSI3,
   TEST_DSI_TMR_SEL_DSI3_if.master TEST_DSI_TMR_SEL_DSI3,
   TEST_DSI_TMR_VAL_DSI3_if.master TEST_DSI_TMR_VAL_DSI3,
   TEST_DSI_TMR_IN_DSI3_if.master TEST_DSI_TMR_IN_DSI3
);

   logic[15:0] data_out_TMR_ANA_DSI3_TX, data_out_TMR_ANA_DSI3_RX, data_out_TMR_DIG_DSI3, data_out_TMR_SEL_DSI3, data_out_TMR_VAL_DSI3, data_out_TMR_IN_DSI3;

   TEST_DSI_TMR_ANA_DSI3_TX #( .reg_addr (base_addr + 'h0), .addr_width(addr_width) ) i_TEST_DSI_TMR_ANA_DSI3_TX ( .data_out (data_out_TMR_ANA_DSI3_TX), .*);
   TEST_DSI_TMR_ANA_DSI3_RX #( .reg_addr (base_addr + 'h1), .addr_width(addr_width) ) i_TEST_DSI_TMR_ANA_DSI3_RX ( .data_out (data_out_TMR_ANA_DSI3_RX), .*);
   TEST_DSI_TMR_DIG_DSI3 #( .reg_addr (base_addr + 'h2), .addr_width(addr_width) ) i_TEST_DSI_TMR_DIG_DSI3 ( .data_out (data_out_TMR_DIG_DSI3), .*);
   TEST_DSI_TMR_SEL_DSI3 #( .reg_addr (base_addr + 'h3), .addr_width(addr_width) ) i_TEST_DSI_TMR_SEL_DSI3 ( .data_out (data_out_TMR_SEL_DSI3), .*);
   TEST_DSI_TMR_VAL_DSI3 #( .reg_addr (base_addr + 'h4), .addr_width(addr_width) ) i_TEST_DSI_TMR_VAL_DSI3 ( .data_out (data_out_TMR_VAL_DSI3), .*);
   TEST_DSI_TMR_IN_DSI3 #( .reg_addr (base_addr + 'h5), .addr_width(addr_width) ) i_TEST_DSI_TMR_IN_DSI3 ( .data_out (data_out_TMR_IN_DSI3), .*);

   // output data assignment
   assign data_out = data_out_TMR_ANA_DSI3_TX | data_out_TMR_ANA_DSI3_RX | data_out_TMR_DIG_DSI3 | data_out_TMR_SEL_DSI3 | data_out_TMR_VAL_DSI3 | data_out_TMR_IN_DSI3;

endmodule : TEST_DSI
