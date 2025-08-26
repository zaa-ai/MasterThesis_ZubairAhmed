/* ###   interfaces   ###################################################### */

// TMR_ANA_TB_PLL
interface TEST_OSC_TMR_ANA_TB_PLL_if;
  logic[15:0] value;
  logic PLL_VTUNE;
  logic PLL_VCTRL;
  logic PLL_PD_N;
  logic PLL_HiZ;
  logic PLL_UP;
  logic PLL_DOWN;
  logic PLL_IC5U;

  modport master (
    output value, PLL_VTUNE, PLL_VCTRL, PLL_PD_N, PLL_HiZ, PLL_UP, PLL_DOWN, PLL_IC5U
  );

  modport slave (
    input value, PLL_VTUNE, PLL_VCTRL, PLL_PD_N, PLL_HiZ, PLL_UP, PLL_DOWN, PLL_IC5U
  );

endinterface : TEST_OSC_TMR_ANA_TB_PLL_if

// TMR_ANA_TB_OSC
interface TEST_OSC_TMR_ANA_TB_OSC_if;
  logic[15:0] value;
  logic OSC_PREAMP;
  logic OSC_SFMAX;
  logic OSC_SFMIN;

  modport master (
    output value, OSC_PREAMP, OSC_SFMAX, OSC_SFMIN
  );

  modport slave (
    input value, OSC_PREAMP, OSC_SFMAX, OSC_SFMIN
  );

endinterface : TEST_OSC_TMR_ANA_TB_OSC_if

// TMR_DIG_TB
interface TEST_OSC_TMR_DIG_TB_if;
  logic[15:0] value;
  logic CLK_AUTO_TRIM_EN;
  logic CLKSW_TST_SEL;
  logic CLKSW_TST_EN;

  modport master (
    output value, CLK_AUTO_TRIM_EN, CLKSW_TST_SEL, CLKSW_TST_EN
  );

  modport slave (
    input value, CLK_AUTO_TRIM_EN, CLKSW_TST_SEL, CLKSW_TST_EN
  );

endinterface : TEST_OSC_TMR_DIG_TB_if

// TMR_VAL_TB
interface TEST_OSC_TMR_VAL_TB_if;
  logic[15:0] value;
  logic PLL_HOLD;
  logic PLL_ON;

  modport master (
    output value, PLL_HOLD, PLL_ON
  );

  modport slave (
    input value, PLL_HOLD, PLL_ON
  );

endinterface : TEST_OSC_TMR_VAL_TB_if

// TMR_SEL_TB
interface TEST_OSC_TMR_SEL_TB_if;
  logic[15:0] value;
  logic PLL_HOLD;
  logic PLL_ON;

  modport master (
    output value, PLL_HOLD, PLL_ON
  );

  modport slave (
    input value, PLL_HOLD, PLL_ON
  );

endinterface : TEST_OSC_TMR_SEL_TB_if



/*###   TMR_ANA_TB_PLL   ######################################################*/
module TEST_OSC_TMR_ANA_TB_PLL #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   TEST_OSC_TMR_ANA_TB_PLL_if.master TEST_OSC_TMR_ANA_TB_PLL);

   // TMR_ANA_TB_PLL : PLL_VTUNE
   logic  PLL_VTUNE, PLL_VTUNE_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       PLL_VTUNE <= 1'b0;
     end
     else begin
       PLL_VTUNE <= PLL_VTUNE_nxt;
     end
   end

   always_comb begin
     PLL_VTUNE_nxt = PLL_VTUNE;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       PLL_VTUNE_nxt = data_in[6:6]; 
     end
   end

   assign TEST_OSC_TMR_ANA_TB_PLL.PLL_VTUNE = PLL_VTUNE;

   // TMR_ANA_TB_PLL : PLL_VCTRL
   logic  PLL_VCTRL, PLL_VCTRL_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       PLL_VCTRL <= 1'b0;
     end
     else begin
       PLL_VCTRL <= PLL_VCTRL_nxt;
     end
   end

   always_comb begin
     PLL_VCTRL_nxt = PLL_VCTRL;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       PLL_VCTRL_nxt = data_in[5:5]; 
     end
   end

   assign TEST_OSC_TMR_ANA_TB_PLL.PLL_VCTRL = PLL_VCTRL;

   // TMR_ANA_TB_PLL : PLL_PD_N
   logic  PLL_PD_N, PLL_PD_N_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       PLL_PD_N <= 1'b0;
     end
     else begin
       PLL_PD_N <= PLL_PD_N_nxt;
     end
   end

   always_comb begin
     PLL_PD_N_nxt = PLL_PD_N;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       PLL_PD_N_nxt = data_in[4:4]; 
     end
   end

   assign TEST_OSC_TMR_ANA_TB_PLL.PLL_PD_N = PLL_PD_N;

   // TMR_ANA_TB_PLL : PLL_HiZ
   logic  PLL_HiZ, PLL_HiZ_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       PLL_HiZ <= 1'b0;
     end
     else begin
       PLL_HiZ <= PLL_HiZ_nxt;
     end
   end

   always_comb begin
     PLL_HiZ_nxt = PLL_HiZ;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       PLL_HiZ_nxt = data_in[3:3]; 
     end
   end

   assign TEST_OSC_TMR_ANA_TB_PLL.PLL_HiZ = PLL_HiZ;

   // TMR_ANA_TB_PLL : PLL_UP
   logic  PLL_UP, PLL_UP_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       PLL_UP <= 1'b0;
     end
     else begin
       PLL_UP <= PLL_UP_nxt;
     end
   end

   always_comb begin
     PLL_UP_nxt = PLL_UP;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       PLL_UP_nxt = data_in[2:2]; 
     end
   end

   assign TEST_OSC_TMR_ANA_TB_PLL.PLL_UP = PLL_UP;

   // TMR_ANA_TB_PLL : PLL_DOWN
   logic  PLL_DOWN, PLL_DOWN_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       PLL_DOWN <= 1'b0;
     end
     else begin
       PLL_DOWN <= PLL_DOWN_nxt;
     end
   end

   always_comb begin
     PLL_DOWN_nxt = PLL_DOWN;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       PLL_DOWN_nxt = data_in[1:1]; 
     end
   end

   assign TEST_OSC_TMR_ANA_TB_PLL.PLL_DOWN = PLL_DOWN;

   // TMR_ANA_TB_PLL : PLL_IC5U
   logic  PLL_IC5U, PLL_IC5U_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       PLL_IC5U <= 1'b0;
     end
     else begin
       PLL_IC5U <= PLL_IC5U_nxt;
     end
   end

   always_comb begin
     PLL_IC5U_nxt = PLL_IC5U;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       PLL_IC5U_nxt = data_in[0:0]; 
     end
   end

   assign TEST_OSC_TMR_ANA_TB_PLL.PLL_IC5U = PLL_IC5U;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {9'd0, PLL_VTUNE, PLL_VCTRL, PLL_PD_N, PLL_HiZ, PLL_UP, PLL_DOWN, PLL_IC5U} : '0;

   assign TEST_OSC_TMR_ANA_TB_PLL.value = {9'd0, PLL_VTUNE, PLL_VCTRL, PLL_PD_N, PLL_HiZ, PLL_UP, PLL_DOWN, PLL_IC5U};

endmodule : TEST_OSC_TMR_ANA_TB_PLL

/*###   TMR_ANA_TB_OSC   ######################################################*/
module TEST_OSC_TMR_ANA_TB_OSC #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   TEST_OSC_TMR_ANA_TB_OSC_if.master TEST_OSC_TMR_ANA_TB_OSC);

   // TMR_ANA_TB_OSC : OSC_PREAMP
   logic  OSC_PREAMP, OSC_PREAMP_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       OSC_PREAMP <= 1'b0;
     end
     else begin
       OSC_PREAMP <= OSC_PREAMP_nxt;
     end
   end

   always_comb begin
     OSC_PREAMP_nxt = OSC_PREAMP;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       OSC_PREAMP_nxt = data_in[2:2]; 
     end
   end

   assign TEST_OSC_TMR_ANA_TB_OSC.OSC_PREAMP = OSC_PREAMP;

   // TMR_ANA_TB_OSC : OSC_SFMAX
   logic  OSC_SFMAX, OSC_SFMAX_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       OSC_SFMAX <= 1'b0;
     end
     else begin
       OSC_SFMAX <= OSC_SFMAX_nxt;
     end
   end

   always_comb begin
     OSC_SFMAX_nxt = OSC_SFMAX;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       OSC_SFMAX_nxt = data_in[1:1]; 
     end
   end

   assign TEST_OSC_TMR_ANA_TB_OSC.OSC_SFMAX = OSC_SFMAX;

   // TMR_ANA_TB_OSC : OSC_SFMIN
   logic  OSC_SFMIN, OSC_SFMIN_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       OSC_SFMIN <= 1'b0;
     end
     else begin
       OSC_SFMIN <= OSC_SFMIN_nxt;
     end
   end

   always_comb begin
     OSC_SFMIN_nxt = OSC_SFMIN;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       OSC_SFMIN_nxt = data_in[0:0]; 
     end
   end

   assign TEST_OSC_TMR_ANA_TB_OSC.OSC_SFMIN = OSC_SFMIN;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {13'd0, OSC_PREAMP, OSC_SFMAX, OSC_SFMIN} : '0;

   assign TEST_OSC_TMR_ANA_TB_OSC.value = {13'd0, OSC_PREAMP, OSC_SFMAX, OSC_SFMIN};

endmodule : TEST_OSC_TMR_ANA_TB_OSC

/*###   TMR_DIG_TB   ######################################################*/
module TEST_OSC_TMR_DIG_TB #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   TEST_OSC_TMR_DIG_TB_if.master TEST_OSC_TMR_DIG_TB);

   // TMR_DIG_TB : CLK_AUTO_TRIM_EN
   logic  CLK_AUTO_TRIM_EN, CLK_AUTO_TRIM_EN_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       CLK_AUTO_TRIM_EN <= 1'b0;
     end
     else begin
       CLK_AUTO_TRIM_EN <= CLK_AUTO_TRIM_EN_nxt;
     end
   end

   always_comb begin
     CLK_AUTO_TRIM_EN_nxt = CLK_AUTO_TRIM_EN;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       CLK_AUTO_TRIM_EN_nxt = data_in[2:2]; 
     end
   end

   assign TEST_OSC_TMR_DIG_TB.CLK_AUTO_TRIM_EN = CLK_AUTO_TRIM_EN;

   // TMR_DIG_TB : CLKSW_TST_SEL
   logic  CLKSW_TST_SEL, CLKSW_TST_SEL_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       CLKSW_TST_SEL <= 1'b0;
     end
     else begin
       CLKSW_TST_SEL <= CLKSW_TST_SEL_nxt;
     end
   end

   always_comb begin
     CLKSW_TST_SEL_nxt = CLKSW_TST_SEL;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       CLKSW_TST_SEL_nxt = data_in[1:1]; 
     end
   end

   assign TEST_OSC_TMR_DIG_TB.CLKSW_TST_SEL = CLKSW_TST_SEL;

   // TMR_DIG_TB : CLKSW_TST_EN
   logic  CLKSW_TST_EN, CLKSW_TST_EN_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       CLKSW_TST_EN <= 1'b0;
     end
     else begin
       CLKSW_TST_EN <= CLKSW_TST_EN_nxt;
     end
   end

   always_comb begin
     CLKSW_TST_EN_nxt = CLKSW_TST_EN;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       CLKSW_TST_EN_nxt = data_in[0:0]; 
     end
   end

   assign TEST_OSC_TMR_DIG_TB.CLKSW_TST_EN = CLKSW_TST_EN;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {13'd0, CLK_AUTO_TRIM_EN, CLKSW_TST_SEL, CLKSW_TST_EN} : '0;

   assign TEST_OSC_TMR_DIG_TB.value = {13'd0, CLK_AUTO_TRIM_EN, CLKSW_TST_SEL, CLKSW_TST_EN};

endmodule : TEST_OSC_TMR_DIG_TB

/*###   TMR_VAL_TB   ######################################################*/
module TEST_OSC_TMR_VAL_TB #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   TEST_OSC_TMR_VAL_TB_if.master TEST_OSC_TMR_VAL_TB);

   // TMR_VAL_TB : PLL_HOLD
   logic  PLL_HOLD, PLL_HOLD_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       PLL_HOLD <= 1'b0;
     end
     else begin
       PLL_HOLD <= PLL_HOLD_nxt;
     end
   end

   always_comb begin
     PLL_HOLD_nxt = PLL_HOLD;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       PLL_HOLD_nxt = data_in[1:1]; 
     end
   end

   assign TEST_OSC_TMR_VAL_TB.PLL_HOLD = PLL_HOLD;

   // TMR_VAL_TB : PLL_ON
   logic  PLL_ON, PLL_ON_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       PLL_ON <= 1'b0;
     end
     else begin
       PLL_ON <= PLL_ON_nxt;
     end
   end

   always_comb begin
     PLL_ON_nxt = PLL_ON;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       PLL_ON_nxt = data_in[0:0]; 
     end
   end

   assign TEST_OSC_TMR_VAL_TB.PLL_ON = PLL_ON;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {14'd0, PLL_HOLD, PLL_ON} : '0;

   assign TEST_OSC_TMR_VAL_TB.value = {14'd0, PLL_HOLD, PLL_ON};

endmodule : TEST_OSC_TMR_VAL_TB

/*###   TMR_SEL_TB   ######################################################*/
module TEST_OSC_TMR_SEL_TB #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   TEST_OSC_TMR_SEL_TB_if.master TEST_OSC_TMR_SEL_TB);

   // TMR_SEL_TB : PLL_HOLD
   logic  PLL_HOLD, PLL_HOLD_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       PLL_HOLD <= 1'b0;
     end
     else begin
       PLL_HOLD <= PLL_HOLD_nxt;
     end
   end

   always_comb begin
     PLL_HOLD_nxt = PLL_HOLD;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       PLL_HOLD_nxt = data_in[1:1]; 
     end
   end

   assign TEST_OSC_TMR_SEL_TB.PLL_HOLD = PLL_HOLD;

   // TMR_SEL_TB : PLL_ON
   logic  PLL_ON, PLL_ON_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       PLL_ON <= 1'b0;
     end
     else begin
       PLL_ON <= PLL_ON_nxt;
     end
   end

   always_comb begin
     PLL_ON_nxt = PLL_ON;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       PLL_ON_nxt = data_in[0:0]; 
     end
   end

   assign TEST_OSC_TMR_SEL_TB.PLL_ON = PLL_ON;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {14'd0, PLL_HOLD, PLL_ON} : '0;

   assign TEST_OSC_TMR_SEL_TB.value = {14'd0, PLL_HOLD, PLL_ON};

endmodule : TEST_OSC_TMR_SEL_TB

/*###   Registers   ######################################################*/
module TEST_OSC #(
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
   TEST_OSC_TMR_ANA_TB_PLL_if.master TEST_OSC_TMR_ANA_TB_PLL,
   TEST_OSC_TMR_ANA_TB_OSC_if.master TEST_OSC_TMR_ANA_TB_OSC,
   TEST_OSC_TMR_DIG_TB_if.master TEST_OSC_TMR_DIG_TB,
   TEST_OSC_TMR_VAL_TB_if.master TEST_OSC_TMR_VAL_TB,
   TEST_OSC_TMR_SEL_TB_if.master TEST_OSC_TMR_SEL_TB
);

   logic[15:0] data_out_TMR_ANA_TB_PLL, data_out_TMR_ANA_TB_OSC, data_out_TMR_DIG_TB, data_out_TMR_VAL_TB, data_out_TMR_SEL_TB;

   TEST_OSC_TMR_ANA_TB_PLL #( .reg_addr (base_addr + 'h0), .addr_width(addr_width) ) i_TEST_OSC_TMR_ANA_TB_PLL ( .data_out (data_out_TMR_ANA_TB_PLL), .*);
   TEST_OSC_TMR_ANA_TB_OSC #( .reg_addr (base_addr + 'h1), .addr_width(addr_width) ) i_TEST_OSC_TMR_ANA_TB_OSC ( .data_out (data_out_TMR_ANA_TB_OSC), .*);
   TEST_OSC_TMR_DIG_TB #( .reg_addr (base_addr + 'h2), .addr_width(addr_width) ) i_TEST_OSC_TMR_DIG_TB ( .data_out (data_out_TMR_DIG_TB), .*);
   TEST_OSC_TMR_VAL_TB #( .reg_addr (base_addr + 'h3), .addr_width(addr_width) ) i_TEST_OSC_TMR_VAL_TB ( .data_out (data_out_TMR_VAL_TB), .*);
   TEST_OSC_TMR_SEL_TB #( .reg_addr (base_addr + 'h4), .addr_width(addr_width) ) i_TEST_OSC_TMR_SEL_TB ( .data_out (data_out_TMR_SEL_TB), .*);

   // output data assignment
   assign data_out = data_out_TMR_ANA_TB_PLL | data_out_TMR_ANA_TB_OSC | data_out_TMR_DIG_TB | data_out_TMR_VAL_TB | data_out_TMR_SEL_TB;

endmodule : TEST_OSC
