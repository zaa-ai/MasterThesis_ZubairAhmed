/* ###   interfaces   ###################################################### */

// TMR_SEL_WS
interface TEST_WS_TMR_SEL_WS_if;
  logic[15:0] value;
  logic DAC;

  modport master (
    output value, DAC
  );

  modport slave (
    input value, DAC
  );

endinterface : TEST_WS_TMR_SEL_WS_if

// TMR_VAL_WS
interface TEST_WS_TMR_VAL_WS_if;
  logic[15:0] value;
  logic[4:0] DAC;

  modport master (
    output value, DAC
  );

  modport slave (
    input value, DAC
  );

endinterface : TEST_WS_TMR_VAL_WS_if



/*###   TMR_SEL_WS   ######################################################*/
module TEST_WS_TMR_SEL_WS #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   TEST_WS_TMR_SEL_WS_if.master TEST_WS_TMR_SEL_WS);

   // TMR_SEL_WS : DAC
   logic  DAC, DAC_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DAC <= 1'b0;
     end
     else begin
       DAC <= DAC_nxt;
     end
   end

   always_comb begin
     DAC_nxt = DAC;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       DAC_nxt = data_in[0:0]; 
     end
   end

   assign TEST_WS_TMR_SEL_WS.DAC = DAC;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {15'd0, DAC} : '0;

   assign TEST_WS_TMR_SEL_WS.value = {15'd0, DAC};

endmodule : TEST_WS_TMR_SEL_WS

/*###   TMR_VAL_WS   ######################################################*/
module TEST_WS_TMR_VAL_WS #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   TEST_WS_TMR_VAL_WS_if.master TEST_WS_TMR_VAL_WS);

   // TMR_VAL_WS : DAC
   logic[4:0]  DAC, DAC_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DAC <= 5'b0;
     end
     else begin
       DAC <= DAC_nxt;
     end
   end

   always_comb begin
     DAC_nxt = DAC;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       DAC_nxt = data_in[4:0]; 
     end
   end

   assign TEST_WS_TMR_VAL_WS.DAC = DAC;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {11'd0, DAC} : '0;

   assign TEST_WS_TMR_VAL_WS.value = {11'd0, DAC};

endmodule : TEST_WS_TMR_VAL_WS

/*###   Registers   ######################################################*/
module TEST_WS #(
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
   TEST_WS_TMR_SEL_WS_if.master TEST_WS_TMR_SEL_WS,
   TEST_WS_TMR_VAL_WS_if.master TEST_WS_TMR_VAL_WS
);

   logic[15:0] data_out_TMR_SEL_WS, data_out_TMR_VAL_WS;

   TEST_WS_TMR_SEL_WS #( .reg_addr (base_addr + 'h0), .addr_width(addr_width) ) i_TEST_WS_TMR_SEL_WS ( .data_out (data_out_TMR_SEL_WS), .*);
   TEST_WS_TMR_VAL_WS #( .reg_addr (base_addr + 'h1), .addr_width(addr_width) ) i_TEST_WS_TMR_VAL_WS ( .data_out (data_out_TMR_VAL_WS), .*);

   // output data assignment
   assign data_out = data_out_TMR_SEL_WS | data_out_TMR_VAL_WS;

endmodule : TEST_WS
