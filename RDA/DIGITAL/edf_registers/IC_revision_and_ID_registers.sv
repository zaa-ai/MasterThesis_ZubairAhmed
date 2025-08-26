/* ###   interfaces   ###################################################### */

// CHIP_ID_LOW
interface IC_revision_and_ID_registers_CHIP_ID_LOW_if;
  logic[15:0] value;
  logic[15:0] CHIP_ID_LOW;

  modport master (
    output value, CHIP_ID_LOW
  );

  modport slave (
    input value, CHIP_ID_LOW
  );

endinterface : IC_revision_and_ID_registers_CHIP_ID_LOW_if

// CHIP_ID_HIGH
interface IC_revision_and_ID_registers_CHIP_ID_HIGH_if;
  logic[15:0] value;
  logic[15:0] CHIP_ID_HIGH;

  modport master (
    output value, CHIP_ID_HIGH
  );

  modport slave (
    input value, CHIP_ID_HIGH
  );

endinterface : IC_revision_and_ID_registers_CHIP_ID_HIGH_if

// IC_REVISION
interface IC_revision_and_ID_registers_IC_REVISION_if;
  logic[15:0] value;
  logic[15:0] REVISION, REVISION_in;

  modport master (
    input REVISION_in, 
    output value, REVISION
  );

  modport slave (
    input value, REVISION, 
    output REVISION_in
  );

endinterface : IC_revision_and_ID_registers_IC_REVISION_if



/*###   CHIP_ID_LOW   ######################################################*/
module IC_revision_and_ID_registers_CHIP_ID_LOW #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   IC_revision_and_ID_registers_CHIP_ID_LOW_if.master IC_revision_and_ID_registers_CHIP_ID_LOW);

   // CHIP_ID_LOW : CHIP_ID_LOW
   logic[15:0]  CHIP_ID_LOW, CHIP_ID_LOW_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       CHIP_ID_LOW <= 16'b0;
     end
     else begin
       CHIP_ID_LOW <= CHIP_ID_LOW_nxt;
     end
   end

   always_comb begin
     CHIP_ID_LOW_nxt = CHIP_ID_LOW;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       CHIP_ID_LOW_nxt = data_in[15:0]; 
     end
   end

   assign IC_revision_and_ID_registers_CHIP_ID_LOW.CHIP_ID_LOW = CHIP_ID_LOW;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {CHIP_ID_LOW} : '0;

   assign IC_revision_and_ID_registers_CHIP_ID_LOW.value = {CHIP_ID_LOW};

endmodule : IC_revision_and_ID_registers_CHIP_ID_LOW

/*###   CHIP_ID_HIGH   ######################################################*/
module IC_revision_and_ID_registers_CHIP_ID_HIGH #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   IC_revision_and_ID_registers_CHIP_ID_HIGH_if.master IC_revision_and_ID_registers_CHIP_ID_HIGH);

   // CHIP_ID_HIGH : CHIP_ID_HIGH
   logic[15:0]  CHIP_ID_HIGH, CHIP_ID_HIGH_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       CHIP_ID_HIGH <= 16'b0;
     end
     else begin
       CHIP_ID_HIGH <= CHIP_ID_HIGH_nxt;
     end
   end

   always_comb begin
     CHIP_ID_HIGH_nxt = CHIP_ID_HIGH;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       CHIP_ID_HIGH_nxt = data_in[15:0]; 
     end
   end

   assign IC_revision_and_ID_registers_CHIP_ID_HIGH.CHIP_ID_HIGH = CHIP_ID_HIGH;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {CHIP_ID_HIGH} : '0;

   assign IC_revision_and_ID_registers_CHIP_ID_HIGH.value = {CHIP_ID_HIGH};

endmodule : IC_revision_and_ID_registers_CHIP_ID_HIGH

/*###   IC_REVISION   ######################################################*/
module IC_revision_and_ID_registers_IC_REVISION #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   input logic[addr_width-1:0] addr,
   input logic           rd,
   output logic[15:0]     data_out,
   IC_revision_and_ID_registers_IC_REVISION_if.master IC_revision_and_ID_registers_IC_REVISION);

   // IC_REVISION : REVISION
   logic[15:0]  REVISION;


   always_comb begin
       REVISION = IC_revision_and_ID_registers_IC_REVISION.REVISION_in;
   end

   assign IC_revision_and_ID_registers_IC_REVISION.REVISION = REVISION;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {REVISION} : '0;

   assign IC_revision_and_ID_registers_IC_REVISION.value = {REVISION};

endmodule : IC_revision_and_ID_registers_IC_REVISION

/*###   Registers   ######################################################*/
module IC_revision_and_ID_registers #(
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
   IC_revision_and_ID_registers_CHIP_ID_LOW_if.master IC_revision_and_ID_registers_CHIP_ID_LOW,
   IC_revision_and_ID_registers_CHIP_ID_HIGH_if.master IC_revision_and_ID_registers_CHIP_ID_HIGH,
   IC_revision_and_ID_registers_IC_REVISION_if.master IC_revision_and_ID_registers_IC_REVISION
);

   logic[15:0] data_out_CHIP_ID_LOW, data_out_CHIP_ID_HIGH, data_out_IC_REVISION;

   IC_revision_and_ID_registers_CHIP_ID_LOW #( .reg_addr (base_addr + 'h1), .addr_width(addr_width) ) i_IC_revision_and_ID_registers_CHIP_ID_LOW ( .data_out (data_out_CHIP_ID_LOW), .*);
   IC_revision_and_ID_registers_CHIP_ID_HIGH #( .reg_addr (base_addr + 'h2), .addr_width(addr_width) ) i_IC_revision_and_ID_registers_CHIP_ID_HIGH ( .data_out (data_out_CHIP_ID_HIGH), .*);
   IC_revision_and_ID_registers_IC_REVISION #( .reg_addr (base_addr + 'h1f), .addr_width(addr_width) ) i_IC_revision_and_ID_registers_IC_REVISION ( .data_out (data_out_IC_REVISION), .*);

   // output data assignment
   assign data_out = data_out_CHIP_ID_LOW | data_out_CHIP_ID_HIGH | data_out_IC_REVISION;

endmodule : IC_revision_and_ID_registers
