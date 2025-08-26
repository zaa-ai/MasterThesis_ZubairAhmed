/* ###   interfaces   ###################################################### */

// OTP_WRITE_PULSE_WIDTH
interface OTP_test_registers_OTP_WRITE_PULSE_WIDTH_if;
  logic[15:0] value;
  logic[11:0] PULSE_WIDTH;

  modport master (
    output value, PULSE_WIDTH
  );

  modport slave (
    input value, PULSE_WIDTH
  );

endinterface : OTP_test_registers_OTP_WRITE_PULSE_WIDTH_if



/*###   OTP_WRITE_PULSE_WIDTH   ######################################################*/
module OTP_test_registers_OTP_WRITE_PULSE_WIDTH #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   OTP_test_registers_OTP_WRITE_PULSE_WIDTH_if.master OTP_test_registers_OTP_WRITE_PULSE_WIDTH);

   // OTP_WRITE_PULSE_WIDTH : PULSE_WIDTH
   logic[11:0]  PULSE_WIDTH, PULSE_WIDTH_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       PULSE_WIDTH <= 12'b11100001000;
     end
     else begin
       PULSE_WIDTH <= PULSE_WIDTH_nxt;
     end
   end

   always_comb begin
     PULSE_WIDTH_nxt = PULSE_WIDTH;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       PULSE_WIDTH_nxt = data_in[11:0]; 
     end
   end

   assign OTP_test_registers_OTP_WRITE_PULSE_WIDTH.PULSE_WIDTH = PULSE_WIDTH;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {4'd0, PULSE_WIDTH} : '0;

   assign OTP_test_registers_OTP_WRITE_PULSE_WIDTH.value = {4'd0, PULSE_WIDTH};

endmodule : OTP_test_registers_OTP_WRITE_PULSE_WIDTH

/*###   Registers   ######################################################*/
module OTP_test_registers #(
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
   OTP_test_registers_OTP_WRITE_PULSE_WIDTH_if.master OTP_test_registers_OTP_WRITE_PULSE_WIDTH
);

   logic[15:0] data_out_OTP_WRITE_PULSE_WIDTH;

   OTP_test_registers_OTP_WRITE_PULSE_WIDTH #( .reg_addr (base_addr + 'haf), .addr_width(addr_width) ) i_OTP_test_registers_OTP_WRITE_PULSE_WIDTH ( .data_out (data_out_OTP_WRITE_PULSE_WIDTH), .*);

   // output data assignment
   assign data_out = data_out_OTP_WRITE_PULSE_WIDTH;

endmodule : OTP_test_registers
