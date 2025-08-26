/* ###   interfaces   ###################################################### */

// TRIM_OSC
interface time_base_registers_TRIM_OSC_if;
  logic[15:0] value;
  logic[6:0] TRIM_OSC, TRIM_OSC_in;
  logic TRIM_OSC_set;

  modport master (
    input TRIM_OSC_in, TRIM_OSC_set, 
    output value, TRIM_OSC
  );

  modport slave (
    input value, TRIM_OSC, 
    output TRIM_OSC_in, TRIM_OSC_set
  );

endinterface : time_base_registers_TRIM_OSC_if

// TRIM_OSC_TCF
interface time_base_registers_TRIM_OSC_TCF_if;
  logic[15:0] value;
  logic[2:0] TCF;

  modport master (
    output value, TCF
  );

  modport slave (
    input value, TCF
  );

endinterface : time_base_registers_TRIM_OSC_TCF_if

// CLKREF_CONF
interface time_base_registers_CLKREF_CONF_if;
  logic[15:0] value;
  logic[1:0] CLKREF_FREQ;

  modport master (
    output value, CLKREF_FREQ
  );

  modport slave (
    input value, CLKREF_FREQ
  );

endinterface : time_base_registers_CLKREF_CONF_if

// TB_CNT
interface time_base_registers_TB_CNT_if;
  logic[15:0] value;
  logic[15:0] CNT, CNT_in;
  logic CNT_set;

  modport master (
    input CNT_in, CNT_set, 
    output value, CNT
  );

  modport slave (
    input value, CNT, 
    output CNT_in, CNT_set
  );

endinterface : time_base_registers_TB_CNT_if



/*###   TRIM_OSC   ######################################################*/
module time_base_registers_TRIM_OSC #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   time_base_registers_TRIM_OSC_if.master time_base_registers_TRIM_OSC);

   // TRIM_OSC : TRIM_OSC
   logic[6:0]  TRIM_OSC, TRIM_OSC_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       TRIM_OSC <= 7'b100000;
     end
     else begin
       TRIM_OSC <= TRIM_OSC_nxt;
     end
   end

   always_comb begin
     TRIM_OSC_nxt = TRIM_OSC;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       TRIM_OSC_nxt = data_in[6:0]; 
     end
     if (time_base_registers_TRIM_OSC.TRIM_OSC_set == 1'b1) begin
       TRIM_OSC_nxt = time_base_registers_TRIM_OSC.TRIM_OSC_in;
     end
   end

   assign time_base_registers_TRIM_OSC.TRIM_OSC = TRIM_OSC;

   `ifdef VCS

     property TRIM_OSC_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (time_base_registers_TRIM_OSC.TRIM_OSC_set !== 1'bx);
     endproperty
      as_TRIM_OSC_set_not_x : assert property (TRIM_OSC_set_not_x) else $error("time_base_registers_TRIM_OSC.TRIM_OSC_set is x after reset");
     cov_TRIM_OSC_set_not_x :  cover property (TRIM_OSC_set_not_x);

   `endif

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {9'd0, TRIM_OSC} : '0;

   assign time_base_registers_TRIM_OSC.value = {9'd0, TRIM_OSC};

endmodule : time_base_registers_TRIM_OSC

/*###   TRIM_OSC_TCF   ######################################################*/
module time_base_registers_TRIM_OSC_TCF #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   time_base_registers_TRIM_OSC_TCF_if.master time_base_registers_TRIM_OSC_TCF);

   // TRIM_OSC_TCF : TCF
   logic[2:0]  TCF, TCF_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       TCF <= 3'b11;
     end
     else begin
       TCF <= TCF_nxt;
     end
   end

   always_comb begin
     TCF_nxt = TCF;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       TCF_nxt = data_in[2:0]; 
     end
   end

   assign time_base_registers_TRIM_OSC_TCF.TCF = TCF;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {13'd0, TCF} : '0;

   assign time_base_registers_TRIM_OSC_TCF.value = {13'd0, TCF};

endmodule : time_base_registers_TRIM_OSC_TCF

/*###   CLKREF_CONF   ######################################################*/
module time_base_registers_CLKREF_CONF #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   time_base_registers_CLKREF_CONF_if.master time_base_registers_CLKREF_CONF);

   // CLKREF_CONF : CLKREF_FREQ
   logic[1:0]  CLKREF_FREQ, CLKREF_FREQ_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       CLKREF_FREQ <= 2'b0;
     end
     else begin
       CLKREF_FREQ <= CLKREF_FREQ_nxt;
     end
   end

   always_comb begin
     CLKREF_FREQ_nxt = CLKREF_FREQ;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       CLKREF_FREQ_nxt = data_in[1:0]; 
     end
   end

   assign time_base_registers_CLKREF_CONF.CLKREF_FREQ = CLKREF_FREQ;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {14'd0, CLKREF_FREQ} : '0;

   assign time_base_registers_CLKREF_CONF.value = {14'd0, CLKREF_FREQ};

endmodule : time_base_registers_CLKREF_CONF

/*###   TB_CNT   ######################################################*/
module time_base_registers_TB_CNT #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic           rd,
   output logic[15:0]     data_out,
   time_base_registers_TB_CNT_if.master time_base_registers_TB_CNT);

   // TB_CNT : CNT
   logic[15:0]  CNT, CNT_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       CNT <= 16'b0;
     end
     else begin
       CNT <= CNT_nxt;
     end
   end

   always_comb begin
     CNT_nxt = CNT;
     if (time_base_registers_TB_CNT.CNT_set == 1'b1) begin
       CNT_nxt = time_base_registers_TB_CNT.CNT_in;
     end
   end

   assign time_base_registers_TB_CNT.CNT = CNT;

   `ifdef VCS

     property CNT_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (time_base_registers_TB_CNT.CNT_set !== 1'bx);
     endproperty
      as_CNT_set_not_x : assert property (CNT_set_not_x) else $error("time_base_registers_TB_CNT.CNT_set is x after reset");
     cov_CNT_set_not_x :  cover property (CNT_set_not_x);

   `endif

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {CNT} : '0;

   assign time_base_registers_TB_CNT.value = {CNT};

endmodule : time_base_registers_TB_CNT

/*###   Registers   ######################################################*/
module time_base_registers #(
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
   time_base_registers_TRIM_OSC_if.master time_base_registers_TRIM_OSC,
   time_base_registers_TRIM_OSC_TCF_if.master time_base_registers_TRIM_OSC_TCF,
   time_base_registers_CLKREF_CONF_if.master time_base_registers_CLKREF_CONF,
   time_base_registers_TB_CNT_if.master time_base_registers_TB_CNT
);

   logic[15:0] data_out_TRIM_OSC, data_out_TRIM_OSC_TCF, data_out_CLKREF_CONF, data_out_TB_CNT;

   time_base_registers_TRIM_OSC #( .reg_addr (base_addr + 'h6), .addr_width(addr_width) ) i_time_base_registers_TRIM_OSC ( .data_out (data_out_TRIM_OSC), .*);
   time_base_registers_TRIM_OSC_TCF #( .reg_addr (base_addr + 'h7), .addr_width(addr_width) ) i_time_base_registers_TRIM_OSC_TCF ( .data_out (data_out_TRIM_OSC_TCF), .*);
   time_base_registers_CLKREF_CONF #( .reg_addr (base_addr + 'h40), .addr_width(addr_width) ) i_time_base_registers_CLKREF_CONF ( .data_out (data_out_CLKREF_CONF), .*);
   time_base_registers_TB_CNT #( .reg_addr (base_addr + 'h41), .addr_width(addr_width) ) i_time_base_registers_TB_CNT ( .data_out (data_out_TB_CNT), .*);

   // output data assignment
   assign data_out = data_out_TRIM_OSC | data_out_TRIM_OSC_TCF | data_out_CLKREF_CONF | data_out_TB_CNT;

endmodule : time_base_registers
