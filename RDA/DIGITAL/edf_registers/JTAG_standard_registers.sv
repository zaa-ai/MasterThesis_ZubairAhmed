/* ###   interfaces   ###################################################### */

// JTAG_ID
interface JTAG_standard_registers_JTAG_ID_if;
  logic[31:0] value;
  logic[15:0] PROJECT;
  logic[10:0] MANUFACTURER;

  modport master (
    output value, PROJECT, MANUFACTURER
  );

  modport slave (
    input value, PROJECT, MANUFACTURER
  );

endinterface : JTAG_standard_registers_JTAG_ID_if

// JTAG_BYPASS
interface JTAG_standard_registers_JTAG_BYPASS_if;
  logic[31:0] value;
  logic JTAG_BYPASS;

  modport master (
    output value, JTAG_BYPASS
  );

  modport slave (
    input value, JTAG_BYPASS
  );

endinterface : JTAG_standard_registers_JTAG_BYPASS_if



/*###   JTAG_ID   ######################################################*/
module JTAG_standard_registers_JTAG_ID #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic           rd,
   output logic[31:0]     data_out,
   JTAG_standard_registers_JTAG_ID_if.master JTAG_standard_registers_JTAG_ID);

   // JTAG_ID : PROJECT
   logic[15:0]  PROJECT, PROJECT_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       PROJECT <= 16'b1100101110110000;
     end
     else begin
       PROJECT <= PROJECT_nxt;
     end
   end

   always_comb begin
     PROJECT_nxt = PROJECT;
   end

   assign JTAG_standard_registers_JTAG_ID.PROJECT = PROJECT;

   // JTAG_ID : MANUFACTURER
   logic[10:0]  MANUFACTURER, MANUFACTURER_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       MANUFACTURER <= 11'b1000101;
     end
     else begin
       MANUFACTURER <= MANUFACTURER_nxt;
     end
   end

   always_comb begin
     MANUFACTURER_nxt = MANUFACTURER;
   end

   assign JTAG_standard_registers_JTAG_ID.MANUFACTURER = MANUFACTURER;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {4'd0, PROJECT, MANUFACTURER, 1'd0} : '0;

   assign JTAG_standard_registers_JTAG_ID.value = {4'd0, PROJECT, MANUFACTURER, 1'd0};

endmodule : JTAG_standard_registers_JTAG_ID

/*###   JTAG_BYPASS   ######################################################*/
module JTAG_standard_registers_JTAG_BYPASS #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[31:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[31:0]     data_out,
   JTAG_standard_registers_JTAG_BYPASS_if.master JTAG_standard_registers_JTAG_BYPASS);

   // JTAG_BYPASS : JTAG_BYPASS
   logic  JTAG_BYPASS, JTAG_BYPASS_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       JTAG_BYPASS <= 1'b0;
     end
     else begin
       JTAG_BYPASS <= JTAG_BYPASS_nxt;
     end
   end

   always_comb begin
     JTAG_BYPASS_nxt = JTAG_BYPASS;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       JTAG_BYPASS_nxt = data_in[0:0]; 
     end
   end

   assign JTAG_standard_registers_JTAG_BYPASS.JTAG_BYPASS = JTAG_BYPASS;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {31'd0, JTAG_BYPASS} : '0;

   assign JTAG_standard_registers_JTAG_BYPASS.value = {31'd0, JTAG_BYPASS};

endmodule : JTAG_standard_registers_JTAG_BYPASS

/*###   Registers   ######################################################*/
module JTAG_standard_registers #(
       parameter base_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[31:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[31:0]     data_out,
   // register interfaces
   JTAG_standard_registers_JTAG_ID_if.master JTAG_standard_registers_JTAG_ID,
   JTAG_standard_registers_JTAG_BYPASS_if.master JTAG_standard_registers_JTAG_BYPASS
);

   logic[31:0] data_out_JTAG_ID, data_out_JTAG_BYPASS;

   JTAG_standard_registers_JTAG_ID #( .reg_addr (base_addr + 'hfb), .addr_width(addr_width) ) i_JTAG_standard_registers_JTAG_ID ( .data_out (data_out_JTAG_ID), .*);
   JTAG_standard_registers_JTAG_BYPASS #( .reg_addr (base_addr + 'hff), .addr_width(addr_width) ) i_JTAG_standard_registers_JTAG_BYPASS ( .data_out (data_out_JTAG_BYPASS), .*);

   // output data assignment
   assign data_out = data_out_JTAG_ID | data_out_JTAG_BYPASS;

endmodule : JTAG_standard_registers
