/* ###   interfaces   ###################################################### */

// TRIM_DSI_REC_FALL
interface DSI3_channel_trimming_registers_TRIM_DSI_REC_FALL_if;
  logic[15:0] value;
  logic[3:0] TRIM_REC2;
  logic[3:0] TRIM_REC1;

  modport master (
    output value, TRIM_REC2, TRIM_REC1
  );

  modport slave (
    input value, TRIM_REC2, TRIM_REC1
  );

endinterface : DSI3_channel_trimming_registers_TRIM_DSI_REC_FALL_if

// TRIM_DSI_REC_RISE
interface DSI3_channel_trimming_registers_TRIM_DSI_REC_RISE_if;
  logic[15:0] value;
  logic[3:0] TRIM_REC2;
  logic[3:0] TRIM_REC1;

  modport master (
    output value, TRIM_REC2, TRIM_REC1
  );

  modport slave (
    input value, TRIM_REC2, TRIM_REC1
  );

endinterface : DSI3_channel_trimming_registers_TRIM_DSI_REC_RISE_if



/*###   TRIM_DSI_REC_FALL   ######################################################*/
module DSI3_channel_trimming_registers_TRIM_DSI_REC_FALL #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   DSI3_channel_trimming_registers_TRIM_DSI_REC_FALL_if.master DSI3_channel_trimming_registers_TRIM_DSI_REC_FALL);

   // TRIM_DSI_REC_FALL : TRIM_REC2
   logic[3:0]  TRIM_REC2, TRIM_REC2_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       TRIM_REC2 <= 4'b0;
     end
     else begin
       TRIM_REC2 <= TRIM_REC2_nxt;
     end
   end

   always_comb begin
     TRIM_REC2_nxt = TRIM_REC2;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       TRIM_REC2_nxt = data_in[7:4]; 
     end
   end

   assign DSI3_channel_trimming_registers_TRIM_DSI_REC_FALL.TRIM_REC2 = TRIM_REC2;

   // TRIM_DSI_REC_FALL : TRIM_REC1
   logic[3:0]  TRIM_REC1, TRIM_REC1_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       TRIM_REC1 <= 4'b0;
     end
     else begin
       TRIM_REC1 <= TRIM_REC1_nxt;
     end
   end

   always_comb begin
     TRIM_REC1_nxt = TRIM_REC1;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       TRIM_REC1_nxt = data_in[3:0]; 
     end
   end

   assign DSI3_channel_trimming_registers_TRIM_DSI_REC_FALL.TRIM_REC1 = TRIM_REC1;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {8'd0, TRIM_REC2, TRIM_REC1} : '0;

   assign DSI3_channel_trimming_registers_TRIM_DSI_REC_FALL.value = {8'd0, TRIM_REC2, TRIM_REC1};

endmodule : DSI3_channel_trimming_registers_TRIM_DSI_REC_FALL

/*###   TRIM_DSI_REC_RISE   ######################################################*/
module DSI3_channel_trimming_registers_TRIM_DSI_REC_RISE #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   DSI3_channel_trimming_registers_TRIM_DSI_REC_RISE_if.master DSI3_channel_trimming_registers_TRIM_DSI_REC_RISE);

   // TRIM_DSI_REC_RISE : TRIM_REC2
   logic[3:0]  TRIM_REC2, TRIM_REC2_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       TRIM_REC2 <= 4'b0;
     end
     else begin
       TRIM_REC2 <= TRIM_REC2_nxt;
     end
   end

   always_comb begin
     TRIM_REC2_nxt = TRIM_REC2;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       TRIM_REC2_nxt = data_in[7:4]; 
     end
   end

   assign DSI3_channel_trimming_registers_TRIM_DSI_REC_RISE.TRIM_REC2 = TRIM_REC2;

   // TRIM_DSI_REC_RISE : TRIM_REC1
   logic[3:0]  TRIM_REC1, TRIM_REC1_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       TRIM_REC1 <= 4'b0;
     end
     else begin
       TRIM_REC1 <= TRIM_REC1_nxt;
     end
   end

   always_comb begin
     TRIM_REC1_nxt = TRIM_REC1;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       TRIM_REC1_nxt = data_in[3:0]; 
     end
   end

   assign DSI3_channel_trimming_registers_TRIM_DSI_REC_RISE.TRIM_REC1 = TRIM_REC1;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {8'd0, TRIM_REC2, TRIM_REC1} : '0;

   assign DSI3_channel_trimming_registers_TRIM_DSI_REC_RISE.value = {8'd0, TRIM_REC2, TRIM_REC1};

endmodule : DSI3_channel_trimming_registers_TRIM_DSI_REC_RISE

/*###   Registers   ######################################################*/
module DSI3_channel_trimming_registers #(
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
   DSI3_channel_trimming_registers_TRIM_DSI_REC_FALL_if.master DSI3_channel_trimming_registers_TRIM_DSI_REC_FALL,
   DSI3_channel_trimming_registers_TRIM_DSI_REC_RISE_if.master DSI3_channel_trimming_registers_TRIM_DSI_REC_RISE
);

   logic[15:0] data_out_TRIM_DSI_REC_FALL, data_out_TRIM_DSI_REC_RISE;

   DSI3_channel_trimming_registers_TRIM_DSI_REC_FALL #( .reg_addr (base_addr + 'h0), .addr_width(addr_width) ) i_DSI3_channel_trimming_registers_TRIM_DSI_REC_FALL ( .data_out (data_out_TRIM_DSI_REC_FALL), .*);
   DSI3_channel_trimming_registers_TRIM_DSI_REC_RISE #( .reg_addr (base_addr + 'h1), .addr_width(addr_width) ) i_DSI3_channel_trimming_registers_TRIM_DSI_REC_RISE ( .data_out (data_out_TRIM_DSI_REC_RISE), .*);

   // output data assignment
   assign data_out = data_out_TRIM_DSI_REC_FALL | data_out_TRIM_DSI_REC_RISE;

endmodule : DSI3_channel_trimming_registers
