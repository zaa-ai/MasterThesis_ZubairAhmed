/* ###   interfaces   ###################################################### */

// SRAM_ECC_CONTROL
interface SRAM_BIST_registers_SRAM_ECC_CONTROL_if;
  logic[15:0] value;
  logic[5:0] ELIP_ECC;
  logic SRAM_ECC_SWAP;
  logic SRAM_ECC_SEL;
  logic[6:0] SRAM_ECC_VAL;

  modport master (
    output value, ELIP_ECC, SRAM_ECC_SWAP, SRAM_ECC_SEL, SRAM_ECC_VAL
  );

  modport slave (
    input value, ELIP_ECC, SRAM_ECC_SWAP, SRAM_ECC_SEL, SRAM_ECC_VAL
  );

endinterface : SRAM_BIST_registers_SRAM_ECC_CONTROL_if

// SRAM_BIST_CTRL
interface SRAM_BIST_registers_SRAM_BIST_CTRL_if;
  logic[15:0] value;
  logic FOUR_6N;
  logic BITWISE;
  logic EN;

  modport master (
    output value, FOUR_6N, BITWISE, EN
  );

  modport slave (
    input value, FOUR_6N, BITWISE, EN
  );

endinterface : SRAM_BIST_registers_SRAM_BIST_CTRL_if

// SRAM_BIST_STAT
interface SRAM_BIST_registers_SRAM_BIST_STAT_if;
  logic[15:0] value;
  logic[1:0] STATUS, STATUS_in;
  logic STATUS_set;

  modport master (
    input STATUS_in, STATUS_set, 
    output value, STATUS
  );

  modport slave (
    input value, STATUS, 
    output STATUS_in, STATUS_set
  );

endinterface : SRAM_BIST_registers_SRAM_BIST_STAT_if



/*###   SRAM_ECC_CONTROL   ######################################################*/
module SRAM_BIST_registers_SRAM_ECC_CONTROL #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   SRAM_BIST_registers_SRAM_ECC_CONTROL_if.master SRAM_BIST_registers_SRAM_ECC_CONTROL);

   // SRAM_ECC_CONTROL : ELIP_ECC
   logic[5:0]  ELIP_ECC, ELIP_ECC_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       ELIP_ECC <= 6'b0;
     end
     else begin
       ELIP_ECC <= ELIP_ECC_nxt;
     end
   end

   always_comb begin
     ELIP_ECC_nxt = ELIP_ECC;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       ELIP_ECC_nxt = data_in[14:9]; 
     end
   end

   assign SRAM_BIST_registers_SRAM_ECC_CONTROL.ELIP_ECC = ELIP_ECC;

   // SRAM_ECC_CONTROL : SRAM_ECC_SWAP
   logic  SRAM_ECC_SWAP, SRAM_ECC_SWAP_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       SRAM_ECC_SWAP <= 1'b0;
     end
     else begin
       SRAM_ECC_SWAP <= SRAM_ECC_SWAP_nxt;
     end
   end

   always_comb begin
     SRAM_ECC_SWAP_nxt = SRAM_ECC_SWAP;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       SRAM_ECC_SWAP_nxt = data_in[8:8]; 
     end
   end

   assign SRAM_BIST_registers_SRAM_ECC_CONTROL.SRAM_ECC_SWAP = SRAM_ECC_SWAP;

   // SRAM_ECC_CONTROL : SRAM_ECC_SEL
   logic  SRAM_ECC_SEL, SRAM_ECC_SEL_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       SRAM_ECC_SEL <= 1'b0;
     end
     else begin
       SRAM_ECC_SEL <= SRAM_ECC_SEL_nxt;
     end
   end

   always_comb begin
     SRAM_ECC_SEL_nxt = SRAM_ECC_SEL;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       SRAM_ECC_SEL_nxt = data_in[7:7]; 
     end
   end

   assign SRAM_BIST_registers_SRAM_ECC_CONTROL.SRAM_ECC_SEL = SRAM_ECC_SEL;

   // SRAM_ECC_CONTROL : SRAM_ECC_VAL
   logic[6:0]  SRAM_ECC_VAL, SRAM_ECC_VAL_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       SRAM_ECC_VAL <= 7'b0;
     end
     else begin
       SRAM_ECC_VAL <= SRAM_ECC_VAL_nxt;
     end
   end

   always_comb begin
     SRAM_ECC_VAL_nxt = SRAM_ECC_VAL;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       SRAM_ECC_VAL_nxt = data_in[6:0]; 
     end
   end

   assign SRAM_BIST_registers_SRAM_ECC_CONTROL.SRAM_ECC_VAL = SRAM_ECC_VAL;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {1'd0, ELIP_ECC, SRAM_ECC_SWAP, SRAM_ECC_SEL, SRAM_ECC_VAL} : '0;

   assign SRAM_BIST_registers_SRAM_ECC_CONTROL.value = {1'd0, ELIP_ECC, SRAM_ECC_SWAP, SRAM_ECC_SEL, SRAM_ECC_VAL};

endmodule : SRAM_BIST_registers_SRAM_ECC_CONTROL

/*###   SRAM_BIST_CTRL   ######################################################*/
module SRAM_BIST_registers_SRAM_BIST_CTRL #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   SRAM_BIST_registers_SRAM_BIST_CTRL_if.master SRAM_BIST_registers_SRAM_BIST_CTRL);

   // SRAM_BIST_CTRL : FOUR_6N
   logic  FOUR_6N, FOUR_6N_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       FOUR_6N <= 1'b0;
     end
     else begin
       FOUR_6N <= FOUR_6N_nxt;
     end
   end

   always_comb begin
     FOUR_6N_nxt = FOUR_6N;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       FOUR_6N_nxt = data_in[2:2]; 
     end
   end

   assign SRAM_BIST_registers_SRAM_BIST_CTRL.FOUR_6N = FOUR_6N;

   // SRAM_BIST_CTRL : BITWISE
   logic  BITWISE, BITWISE_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       BITWISE <= 1'b0;
     end
     else begin
       BITWISE <= BITWISE_nxt;
     end
   end

   always_comb begin
     BITWISE_nxt = BITWISE;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       BITWISE_nxt = data_in[1:1]; 
     end
   end

   assign SRAM_BIST_registers_SRAM_BIST_CTRL.BITWISE = BITWISE;

   // SRAM_BIST_CTRL : EN
   logic  EN, EN_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       EN <= 1'b0;
     end
     else begin
       EN <= EN_nxt;
     end
   end

   always_comb begin
     EN_nxt = EN;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       EN_nxt = data_in[0:0]; 
     end
   end

   assign SRAM_BIST_registers_SRAM_BIST_CTRL.EN = EN;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {13'd0, FOUR_6N, BITWISE, EN} : '0;

   assign SRAM_BIST_registers_SRAM_BIST_CTRL.value = {13'd0, FOUR_6N, BITWISE, EN};

endmodule : SRAM_BIST_registers_SRAM_BIST_CTRL

/*###   SRAM_BIST_STAT   ######################################################*/
module SRAM_BIST_registers_SRAM_BIST_STAT #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic           rd,
   output logic[15:0]     data_out,
   SRAM_BIST_registers_SRAM_BIST_STAT_if.master SRAM_BIST_registers_SRAM_BIST_STAT);

   // SRAM_BIST_STAT : STATUS
   logic[1:0]  STATUS, STATUS_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       STATUS <= 2'b0;
     end
     else begin
       STATUS <= STATUS_nxt;
     end
   end

   always_comb begin
     STATUS_nxt = STATUS;
     if (SRAM_BIST_registers_SRAM_BIST_STAT.STATUS_set == 1'b1) begin
       STATUS_nxt = SRAM_BIST_registers_SRAM_BIST_STAT.STATUS_in;
     end
   end

   assign SRAM_BIST_registers_SRAM_BIST_STAT.STATUS = STATUS;

   `ifdef VCS

     property STATUS_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (SRAM_BIST_registers_SRAM_BIST_STAT.STATUS_set !== 1'bx);
     endproperty
      as_STATUS_set_not_x : assert property (STATUS_set_not_x) else $error("SRAM_BIST_registers_SRAM_BIST_STAT.STATUS_set is x after reset");
     cov_STATUS_set_not_x :  cover property (STATUS_set_not_x);

   `endif

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {14'd0, STATUS} : '0;

   assign SRAM_BIST_registers_SRAM_BIST_STAT.value = {14'd0, STATUS};

endmodule : SRAM_BIST_registers_SRAM_BIST_STAT

/*###   Registers   ######################################################*/
module SRAM_BIST_registers #(
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
   SRAM_BIST_registers_SRAM_ECC_CONTROL_if.master SRAM_BIST_registers_SRAM_ECC_CONTROL,
   SRAM_BIST_registers_SRAM_BIST_CTRL_if.master SRAM_BIST_registers_SRAM_BIST_CTRL,
   SRAM_BIST_registers_SRAM_BIST_STAT_if.master SRAM_BIST_registers_SRAM_BIST_STAT
);

   logic[15:0] data_out_SRAM_ECC_CONTROL, data_out_SRAM_BIST_CTRL, data_out_SRAM_BIST_STAT;

   SRAM_BIST_registers_SRAM_ECC_CONTROL #( .reg_addr (base_addr + 'h7), .addr_width(addr_width) ) i_SRAM_BIST_registers_SRAM_ECC_CONTROL ( .data_out (data_out_SRAM_ECC_CONTROL), .*);
   SRAM_BIST_registers_SRAM_BIST_CTRL #( .reg_addr (base_addr + 'h8), .addr_width(addr_width) ) i_SRAM_BIST_registers_SRAM_BIST_CTRL ( .data_out (data_out_SRAM_BIST_CTRL), .*);
   SRAM_BIST_registers_SRAM_BIST_STAT #( .reg_addr (base_addr + 'h9), .addr_width(addr_width) ) i_SRAM_BIST_registers_SRAM_BIST_STAT ( .data_out (data_out_SRAM_BIST_STAT), .*);

   // output data assignment
   assign data_out = data_out_SRAM_ECC_CONTROL | data_out_SRAM_BIST_CTRL | data_out_SRAM_BIST_STAT;

endmodule : SRAM_BIST_registers
