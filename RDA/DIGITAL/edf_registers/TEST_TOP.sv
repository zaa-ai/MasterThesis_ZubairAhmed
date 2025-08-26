/* ###   interfaces   ###################################################### */

// TMR_ANA
interface TEST_TOP_TMR_ANA_if;
  logic[15:0] value;
  logic ENABLE_ATB;

  modport master (
    output value, ENABLE_ATB
  );

  modport slave (
    input value, ENABLE_ATB
  );

endinterface : TEST_TOP_TMR_ANA_if

// TMR_DIG
interface TEST_TOP_TMR_DIG_if;
  logic[15:0] value;
  logic IGNORE_OSC_READY;
  logic SEL_SYNC;
  logic USE_JTAG;

  modport master (
    output value, IGNORE_OSC_READY, SEL_SYNC, USE_JTAG
  );

  modport slave (
    input value, IGNORE_OSC_READY, SEL_SYNC, USE_JTAG
  );

endinterface : TEST_TOP_TMR_DIG_if

// TMR_IN
interface TEST_TOP_TMR_IN_if;
  logic[15:0] value;
  logic[3:0] tmr_in_3;
  logic[3:0] tmr_in_2;
  logic[3:0] tmr_in_1;
  logic[3:0] tmr_in_0;

  modport master (
    output value, tmr_in_3, tmr_in_2, tmr_in_1, tmr_in_0
  );

  modport slave (
    input value, tmr_in_3, tmr_in_2, tmr_in_1, tmr_in_0
  );

endinterface : TEST_TOP_TMR_IN_if

// TMR_OUT_CSB_SCK
interface TEST_TOP_TMR_OUT_CSB_SCK_if;
  logic[15:0] value;
  logic EN_CSB;
  logic[5:0] SEL_CSB;
  logic EN_SCK;
  logic[5:0] SEL_SCK;

  modport master (
    output value, EN_CSB, SEL_CSB, EN_SCK, SEL_SCK
  );

  modport slave (
    input value, EN_CSB, SEL_CSB, EN_SCK, SEL_SCK
  );

endinterface : TEST_TOP_TMR_OUT_CSB_SCK_if

// TMR_OUT_MOSI_MISO
interface TEST_TOP_TMR_OUT_MOSI_MISO_if;
  logic[15:0] value;
  logic EN_MOSI;
  logic[5:0] SEL_MOSI;
  logic EN_MISO;
  logic[5:0] SEL_MISO;

  modport master (
    output value, EN_MOSI, SEL_MOSI, EN_MISO, SEL_MISO
  );

  modport slave (
    input value, EN_MOSI, SEL_MOSI, EN_MISO, SEL_MISO
  );

endinterface : TEST_TOP_TMR_OUT_MOSI_MISO_if

// TMR_OUT_BFWB_SYNCB
interface TEST_TOP_TMR_OUT_BFWB_SYNCB_if;
  logic[15:0] value;
  logic EN_BFWB;
  logic[5:0] SEL_BFWB;
  logic EN_SYNCB;
  logic[5:0] SEL_SYNCB;

  modport master (
    output value, EN_BFWB, SEL_BFWB, EN_SYNCB, SEL_SYNCB
  );

  modport slave (
    input value, EN_BFWB, SEL_BFWB, EN_SYNCB, SEL_SYNCB
  );

endinterface : TEST_TOP_TMR_OUT_BFWB_SYNCB_if

// TMR_OUT_DAB_INTB
interface TEST_TOP_TMR_OUT_DAB_INTB_if;
  logic[15:0] value;
  logic EN_DAB;
  logic[5:0] SEL_DAB;
  logic EN_INTB;
  logic[5:0] SEL_INTB;

  modport master (
    output value, EN_DAB, SEL_DAB, EN_INTB, SEL_INTB
  );

  modport slave (
    input value, EN_DAB, SEL_DAB, EN_INTB, SEL_INTB
  );

endinterface : TEST_TOP_TMR_OUT_DAB_INTB_if

// TMR_OUT_RFC
interface TEST_TOP_TMR_OUT_RFC_if;
  logic[15:0] value;
  logic EN_RFC;
  logic[5:0] SEL_RFC;

  modport master (
    output value, EN_RFC, SEL_RFC
  );

  modport slave (
    input value, EN_RFC, SEL_RFC
  );

endinterface : TEST_TOP_TMR_OUT_RFC_if



/*###   TMR_ANA   ######################################################*/
module TEST_TOP_TMR_ANA #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   TEST_TOP_TMR_ANA_if.master TEST_TOP_TMR_ANA);

   // TMR_ANA : ENABLE_ATB
   logic  ENABLE_ATB, ENABLE_ATB_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       ENABLE_ATB <= 1'b0;
     end
     else begin
       ENABLE_ATB <= ENABLE_ATB_nxt;
     end
   end

   always_comb begin
     ENABLE_ATB_nxt = ENABLE_ATB;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       ENABLE_ATB_nxt = data_in[0:0]; 
     end
   end

   assign TEST_TOP_TMR_ANA.ENABLE_ATB = ENABLE_ATB;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {15'd0, ENABLE_ATB} : '0;

   assign TEST_TOP_TMR_ANA.value = {15'd0, ENABLE_ATB};

endmodule : TEST_TOP_TMR_ANA

/*###   TMR_DIG   ######################################################*/
module TEST_TOP_TMR_DIG #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   TEST_TOP_TMR_DIG_if.master TEST_TOP_TMR_DIG);

   // TMR_DIG : IGNORE_OSC_READY
   logic  IGNORE_OSC_READY, IGNORE_OSC_READY_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       IGNORE_OSC_READY <= 1'b0;
     end
     else begin
       IGNORE_OSC_READY <= IGNORE_OSC_READY_nxt;
     end
   end

   always_comb begin
     IGNORE_OSC_READY_nxt = IGNORE_OSC_READY;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       IGNORE_OSC_READY_nxt = data_in[2:2]; 
     end
   end

   assign TEST_TOP_TMR_DIG.IGNORE_OSC_READY = IGNORE_OSC_READY;

   // TMR_DIG : SEL_SYNC
   logic  SEL_SYNC, SEL_SYNC_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       SEL_SYNC <= 1'b0;
     end
     else begin
       SEL_SYNC <= SEL_SYNC_nxt;
     end
   end

   always_comb begin
     SEL_SYNC_nxt = SEL_SYNC;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       SEL_SYNC_nxt = data_in[1:1]; 
     end
   end

   assign TEST_TOP_TMR_DIG.SEL_SYNC = SEL_SYNC;

   // TMR_DIG : USE_JTAG
   logic  USE_JTAG, USE_JTAG_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       USE_JTAG <= 1'b0;
     end
     else begin
       USE_JTAG <= USE_JTAG_nxt;
     end
   end

   always_comb begin
     USE_JTAG_nxt = USE_JTAG;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       USE_JTAG_nxt = data_in[0:0]; 
     end
   end

   assign TEST_TOP_TMR_DIG.USE_JTAG = USE_JTAG;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {13'd0, IGNORE_OSC_READY, SEL_SYNC, USE_JTAG} : '0;

   assign TEST_TOP_TMR_DIG.value = {13'd0, IGNORE_OSC_READY, SEL_SYNC, USE_JTAG};

endmodule : TEST_TOP_TMR_DIG

/*###   TMR_IN   ######################################################*/
module TEST_TOP_TMR_IN #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   TEST_TOP_TMR_IN_if.master TEST_TOP_TMR_IN);

   // TMR_IN : tmr_in_3
   logic[3:0]  tmr_in_3, tmr_in_3_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       tmr_in_3 <= 4'b0;
     end
     else begin
       tmr_in_3 <= tmr_in_3_nxt;
     end
   end

   always_comb begin
     tmr_in_3_nxt = tmr_in_3;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       tmr_in_3_nxt = data_in[15:12]; 
     end
   end

   assign TEST_TOP_TMR_IN.tmr_in_3 = tmr_in_3;

   // TMR_IN : tmr_in_2
   logic[3:0]  tmr_in_2, tmr_in_2_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       tmr_in_2 <= 4'b0;
     end
     else begin
       tmr_in_2 <= tmr_in_2_nxt;
     end
   end

   always_comb begin
     tmr_in_2_nxt = tmr_in_2;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       tmr_in_2_nxt = data_in[11:8]; 
     end
   end

   assign TEST_TOP_TMR_IN.tmr_in_2 = tmr_in_2;

   // TMR_IN : tmr_in_1
   logic[3:0]  tmr_in_1, tmr_in_1_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       tmr_in_1 <= 4'b0;
     end
     else begin
       tmr_in_1 <= tmr_in_1_nxt;
     end
   end

   always_comb begin
     tmr_in_1_nxt = tmr_in_1;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       tmr_in_1_nxt = data_in[7:4]; 
     end
   end

   assign TEST_TOP_TMR_IN.tmr_in_1 = tmr_in_1;

   // TMR_IN : tmr_in_0
   logic[3:0]  tmr_in_0, tmr_in_0_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       tmr_in_0 <= 4'b0;
     end
     else begin
       tmr_in_0 <= tmr_in_0_nxt;
     end
   end

   always_comb begin
     tmr_in_0_nxt = tmr_in_0;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       tmr_in_0_nxt = data_in[3:0]; 
     end
   end

   assign TEST_TOP_TMR_IN.tmr_in_0 = tmr_in_0;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {tmr_in_3, tmr_in_2, tmr_in_1, tmr_in_0} : '0;

   assign TEST_TOP_TMR_IN.value = {tmr_in_3, tmr_in_2, tmr_in_1, tmr_in_0};

endmodule : TEST_TOP_TMR_IN

/*###   TMR_OUT_CSB_SCK   ######################################################*/
module TEST_TOP_TMR_OUT_CSB_SCK #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   TEST_TOP_TMR_OUT_CSB_SCK_if.master TEST_TOP_TMR_OUT_CSB_SCK);

   // TMR_OUT_CSB_SCK : EN_CSB
   logic  EN_CSB, EN_CSB_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       EN_CSB <= 1'b0;
     end
     else begin
       EN_CSB <= EN_CSB_nxt;
     end
   end

   always_comb begin
     EN_CSB_nxt = EN_CSB;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       EN_CSB_nxt = data_in[15:15]; 
     end
   end

   assign TEST_TOP_TMR_OUT_CSB_SCK.EN_CSB = EN_CSB;

   // TMR_OUT_CSB_SCK : SEL_CSB
   logic[5:0]  SEL_CSB, SEL_CSB_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       SEL_CSB <= 6'b0;
     end
     else begin
       SEL_CSB <= SEL_CSB_nxt;
     end
   end

   always_comb begin
     SEL_CSB_nxt = SEL_CSB;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       SEL_CSB_nxt = data_in[13:8]; 
     end
   end

   assign TEST_TOP_TMR_OUT_CSB_SCK.SEL_CSB = SEL_CSB;

   // TMR_OUT_CSB_SCK : EN_SCK
   logic  EN_SCK, EN_SCK_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       EN_SCK <= 1'b0;
     end
     else begin
       EN_SCK <= EN_SCK_nxt;
     end
   end

   always_comb begin
     EN_SCK_nxt = EN_SCK;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       EN_SCK_nxt = data_in[7:7]; 
     end
   end

   assign TEST_TOP_TMR_OUT_CSB_SCK.EN_SCK = EN_SCK;

   // TMR_OUT_CSB_SCK : SEL_SCK
   logic[5:0]  SEL_SCK, SEL_SCK_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       SEL_SCK <= 6'b0;
     end
     else begin
       SEL_SCK <= SEL_SCK_nxt;
     end
   end

   always_comb begin
     SEL_SCK_nxt = SEL_SCK;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       SEL_SCK_nxt = data_in[5:0]; 
     end
   end

   assign TEST_TOP_TMR_OUT_CSB_SCK.SEL_SCK = SEL_SCK;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {EN_CSB, 1'd0, SEL_CSB, EN_SCK, 1'd0, SEL_SCK} : '0;

   assign TEST_TOP_TMR_OUT_CSB_SCK.value = {EN_CSB, 1'd0, SEL_CSB, EN_SCK, 1'd0, SEL_SCK};

endmodule : TEST_TOP_TMR_OUT_CSB_SCK

/*###   TMR_OUT_MOSI_MISO   ######################################################*/
module TEST_TOP_TMR_OUT_MOSI_MISO #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   TEST_TOP_TMR_OUT_MOSI_MISO_if.master TEST_TOP_TMR_OUT_MOSI_MISO);

   // TMR_OUT_MOSI_MISO : EN_MOSI
   logic  EN_MOSI, EN_MOSI_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       EN_MOSI <= 1'b0;
     end
     else begin
       EN_MOSI <= EN_MOSI_nxt;
     end
   end

   always_comb begin
     EN_MOSI_nxt = EN_MOSI;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       EN_MOSI_nxt = data_in[15:15]; 
     end
   end

   assign TEST_TOP_TMR_OUT_MOSI_MISO.EN_MOSI = EN_MOSI;

   // TMR_OUT_MOSI_MISO : SEL_MOSI
   logic[5:0]  SEL_MOSI, SEL_MOSI_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       SEL_MOSI <= 6'b0;
     end
     else begin
       SEL_MOSI <= SEL_MOSI_nxt;
     end
   end

   always_comb begin
     SEL_MOSI_nxt = SEL_MOSI;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       SEL_MOSI_nxt = data_in[13:8]; 
     end
   end

   assign TEST_TOP_TMR_OUT_MOSI_MISO.SEL_MOSI = SEL_MOSI;

   // TMR_OUT_MOSI_MISO : EN_MISO
   logic  EN_MISO, EN_MISO_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       EN_MISO <= 1'b0;
     end
     else begin
       EN_MISO <= EN_MISO_nxt;
     end
   end

   always_comb begin
     EN_MISO_nxt = EN_MISO;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       EN_MISO_nxt = data_in[7:7]; 
     end
   end

   assign TEST_TOP_TMR_OUT_MOSI_MISO.EN_MISO = EN_MISO;

   // TMR_OUT_MOSI_MISO : SEL_MISO
   logic[5:0]  SEL_MISO, SEL_MISO_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       SEL_MISO <= 6'b0;
     end
     else begin
       SEL_MISO <= SEL_MISO_nxt;
     end
   end

   always_comb begin
     SEL_MISO_nxt = SEL_MISO;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       SEL_MISO_nxt = data_in[5:0]; 
     end
   end

   assign TEST_TOP_TMR_OUT_MOSI_MISO.SEL_MISO = SEL_MISO;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {EN_MOSI, 1'd0, SEL_MOSI, EN_MISO, 1'd0, SEL_MISO} : '0;

   assign TEST_TOP_TMR_OUT_MOSI_MISO.value = {EN_MOSI, 1'd0, SEL_MOSI, EN_MISO, 1'd0, SEL_MISO};

endmodule : TEST_TOP_TMR_OUT_MOSI_MISO

/*###   TMR_OUT_BFWB_SYNCB   ######################################################*/
module TEST_TOP_TMR_OUT_BFWB_SYNCB #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   TEST_TOP_TMR_OUT_BFWB_SYNCB_if.master TEST_TOP_TMR_OUT_BFWB_SYNCB);

   // TMR_OUT_BFWB_SYNCB : EN_BFWB
   logic  EN_BFWB, EN_BFWB_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       EN_BFWB <= 1'b0;
     end
     else begin
       EN_BFWB <= EN_BFWB_nxt;
     end
   end

   always_comb begin
     EN_BFWB_nxt = EN_BFWB;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       EN_BFWB_nxt = data_in[15:15]; 
     end
   end

   assign TEST_TOP_TMR_OUT_BFWB_SYNCB.EN_BFWB = EN_BFWB;

   // TMR_OUT_BFWB_SYNCB : SEL_BFWB
   logic[5:0]  SEL_BFWB, SEL_BFWB_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       SEL_BFWB <= 6'b0;
     end
     else begin
       SEL_BFWB <= SEL_BFWB_nxt;
     end
   end

   always_comb begin
     SEL_BFWB_nxt = SEL_BFWB;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       SEL_BFWB_nxt = data_in[13:8]; 
     end
   end

   assign TEST_TOP_TMR_OUT_BFWB_SYNCB.SEL_BFWB = SEL_BFWB;

   // TMR_OUT_BFWB_SYNCB : EN_SYNCB
   logic  EN_SYNCB, EN_SYNCB_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       EN_SYNCB <= 1'b0;
     end
     else begin
       EN_SYNCB <= EN_SYNCB_nxt;
     end
   end

   always_comb begin
     EN_SYNCB_nxt = EN_SYNCB;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       EN_SYNCB_nxt = data_in[7:7]; 
     end
   end

   assign TEST_TOP_TMR_OUT_BFWB_SYNCB.EN_SYNCB = EN_SYNCB;

   // TMR_OUT_BFWB_SYNCB : SEL_SYNCB
   logic[5:0]  SEL_SYNCB, SEL_SYNCB_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       SEL_SYNCB <= 6'b0;
     end
     else begin
       SEL_SYNCB <= SEL_SYNCB_nxt;
     end
   end

   always_comb begin
     SEL_SYNCB_nxt = SEL_SYNCB;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       SEL_SYNCB_nxt = data_in[5:0]; 
     end
   end

   assign TEST_TOP_TMR_OUT_BFWB_SYNCB.SEL_SYNCB = SEL_SYNCB;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {EN_BFWB, 1'd0, SEL_BFWB, EN_SYNCB, 1'd0, SEL_SYNCB} : '0;

   assign TEST_TOP_TMR_OUT_BFWB_SYNCB.value = {EN_BFWB, 1'd0, SEL_BFWB, EN_SYNCB, 1'd0, SEL_SYNCB};

endmodule : TEST_TOP_TMR_OUT_BFWB_SYNCB

/*###   TMR_OUT_DAB_INTB   ######################################################*/
module TEST_TOP_TMR_OUT_DAB_INTB #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   TEST_TOP_TMR_OUT_DAB_INTB_if.master TEST_TOP_TMR_OUT_DAB_INTB);

   // TMR_OUT_DAB_INTB : EN_DAB
   logic  EN_DAB, EN_DAB_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       EN_DAB <= 1'b0;
     end
     else begin
       EN_DAB <= EN_DAB_nxt;
     end
   end

   always_comb begin
     EN_DAB_nxt = EN_DAB;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       EN_DAB_nxt = data_in[15:15]; 
     end
   end

   assign TEST_TOP_TMR_OUT_DAB_INTB.EN_DAB = EN_DAB;

   // TMR_OUT_DAB_INTB : SEL_DAB
   logic[5:0]  SEL_DAB, SEL_DAB_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       SEL_DAB <= 6'b0;
     end
     else begin
       SEL_DAB <= SEL_DAB_nxt;
     end
   end

   always_comb begin
     SEL_DAB_nxt = SEL_DAB;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       SEL_DAB_nxt = data_in[13:8]; 
     end
   end

   assign TEST_TOP_TMR_OUT_DAB_INTB.SEL_DAB = SEL_DAB;

   // TMR_OUT_DAB_INTB : EN_INTB
   logic  EN_INTB, EN_INTB_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       EN_INTB <= 1'b0;
     end
     else begin
       EN_INTB <= EN_INTB_nxt;
     end
   end

   always_comb begin
     EN_INTB_nxt = EN_INTB;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       EN_INTB_nxt = data_in[7:7]; 
     end
   end

   assign TEST_TOP_TMR_OUT_DAB_INTB.EN_INTB = EN_INTB;

   // TMR_OUT_DAB_INTB : SEL_INTB
   logic[5:0]  SEL_INTB, SEL_INTB_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       SEL_INTB <= 6'b0;
     end
     else begin
       SEL_INTB <= SEL_INTB_nxt;
     end
   end

   always_comb begin
     SEL_INTB_nxt = SEL_INTB;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       SEL_INTB_nxt = data_in[5:0]; 
     end
   end

   assign TEST_TOP_TMR_OUT_DAB_INTB.SEL_INTB = SEL_INTB;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {EN_DAB, 1'd0, SEL_DAB, EN_INTB, 1'd0, SEL_INTB} : '0;

   assign TEST_TOP_TMR_OUT_DAB_INTB.value = {EN_DAB, 1'd0, SEL_DAB, EN_INTB, 1'd0, SEL_INTB};

endmodule : TEST_TOP_TMR_OUT_DAB_INTB

/*###   TMR_OUT_RFC   ######################################################*/
module TEST_TOP_TMR_OUT_RFC #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   TEST_TOP_TMR_OUT_RFC_if.master TEST_TOP_TMR_OUT_RFC);

   // TMR_OUT_RFC : EN_RFC
   logic  EN_RFC, EN_RFC_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       EN_RFC <= 1'b0;
     end
     else begin
       EN_RFC <= EN_RFC_nxt;
     end
   end

   always_comb begin
     EN_RFC_nxt = EN_RFC;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       EN_RFC_nxt = data_in[7:7]; 
     end
   end

   assign TEST_TOP_TMR_OUT_RFC.EN_RFC = EN_RFC;

   // TMR_OUT_RFC : SEL_RFC
   logic[5:0]  SEL_RFC, SEL_RFC_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       SEL_RFC <= 6'b0;
     end
     else begin
       SEL_RFC <= SEL_RFC_nxt;
     end
   end

   always_comb begin
     SEL_RFC_nxt = SEL_RFC;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       SEL_RFC_nxt = data_in[5:0]; 
     end
   end

   assign TEST_TOP_TMR_OUT_RFC.SEL_RFC = SEL_RFC;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {8'd0, EN_RFC, 1'd0, SEL_RFC} : '0;

   assign TEST_TOP_TMR_OUT_RFC.value = {8'd0, EN_RFC, 1'd0, SEL_RFC};

endmodule : TEST_TOP_TMR_OUT_RFC

/*###   Registers   ######################################################*/
module TEST_TOP #(
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
   TEST_TOP_TMR_ANA_if.master TEST_TOP_TMR_ANA,
   TEST_TOP_TMR_DIG_if.master TEST_TOP_TMR_DIG,
   TEST_TOP_TMR_IN_if.master TEST_TOP_TMR_IN,
   TEST_TOP_TMR_OUT_CSB_SCK_if.master TEST_TOP_TMR_OUT_CSB_SCK,
   TEST_TOP_TMR_OUT_MOSI_MISO_if.master TEST_TOP_TMR_OUT_MOSI_MISO,
   TEST_TOP_TMR_OUT_BFWB_SYNCB_if.master TEST_TOP_TMR_OUT_BFWB_SYNCB,
   TEST_TOP_TMR_OUT_DAB_INTB_if.master TEST_TOP_TMR_OUT_DAB_INTB,
   TEST_TOP_TMR_OUT_RFC_if.master TEST_TOP_TMR_OUT_RFC
);

   logic[15:0] data_out_TMR_ANA, data_out_TMR_DIG, data_out_TMR_IN, data_out_TMR_OUT_CSB_SCK, data_out_TMR_OUT_MOSI_MISO, data_out_TMR_OUT_BFWB_SYNCB, data_out_TMR_OUT_DAB_INTB, data_out_TMR_OUT_RFC;

   TEST_TOP_TMR_ANA #( .reg_addr (base_addr + 'h1), .addr_width(addr_width) ) i_TEST_TOP_TMR_ANA ( .data_out (data_out_TMR_ANA), .*);
   TEST_TOP_TMR_DIG #( .reg_addr (base_addr + 'h2), .addr_width(addr_width) ) i_TEST_TOP_TMR_DIG ( .data_out (data_out_TMR_DIG), .*);
   TEST_TOP_TMR_IN #( .reg_addr (base_addr + 'h5), .addr_width(addr_width) ) i_TEST_TOP_TMR_IN ( .data_out (data_out_TMR_IN), .*);
   TEST_TOP_TMR_OUT_CSB_SCK #( .reg_addr (base_addr + 'h6), .addr_width(addr_width) ) i_TEST_TOP_TMR_OUT_CSB_SCK ( .data_out (data_out_TMR_OUT_CSB_SCK), .*);
   TEST_TOP_TMR_OUT_MOSI_MISO #( .reg_addr (base_addr + 'h7), .addr_width(addr_width) ) i_TEST_TOP_TMR_OUT_MOSI_MISO ( .data_out (data_out_TMR_OUT_MOSI_MISO), .*);
   TEST_TOP_TMR_OUT_BFWB_SYNCB #( .reg_addr (base_addr + 'h8), .addr_width(addr_width) ) i_TEST_TOP_TMR_OUT_BFWB_SYNCB ( .data_out (data_out_TMR_OUT_BFWB_SYNCB), .*);
   TEST_TOP_TMR_OUT_DAB_INTB #( .reg_addr (base_addr + 'h9), .addr_width(addr_width) ) i_TEST_TOP_TMR_OUT_DAB_INTB ( .data_out (data_out_TMR_OUT_DAB_INTB), .*);
   TEST_TOP_TMR_OUT_RFC #( .reg_addr (base_addr + 'ha), .addr_width(addr_width) ) i_TEST_TOP_TMR_OUT_RFC ( .data_out (data_out_TMR_OUT_RFC), .*);

   // output data assignment
   assign data_out = data_out_TMR_ANA | data_out_TMR_DIG | data_out_TMR_IN | data_out_TMR_OUT_CSB_SCK | data_out_TMR_OUT_MOSI_MISO | data_out_TMR_OUT_BFWB_SYNCB | data_out_TMR_OUT_DAB_INTB | data_out_TMR_OUT_RFC;

endmodule : TEST_TOP
