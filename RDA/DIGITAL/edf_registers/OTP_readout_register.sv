/* ###   interfaces   ###################################################### */

// OTP_READ_ADDRESS
interface OTP_readout_register_OTP_READ_ADDRESS_if;
  logic[15:0] value;
  logic access_wr;
  logic access_rd;
  logic[11:0] ADDR;

  modport master (
    output value, access_wr, access_rd, ADDR
  );

  modport slave (
    input value, access_wr, access_rd, ADDR
  );

endinterface : OTP_readout_register_OTP_READ_ADDRESS_if

// OTP_READ_VALUE
interface OTP_readout_register_OTP_READ_VALUE_if;
  logic[15:0] value;
  logic[3:0] ECC, ECC_in;
  logic[7:0] VALUE, VALUE_in;
  logic ECC_set, VALUE_set;

  modport master (
    input ECC_in, VALUE_in, ECC_set, VALUE_set, 
    output value, ECC, VALUE
  );

  modport slave (
    input value, ECC, VALUE, 
    output ECC_in, VALUE_in, ECC_set, VALUE_set
  );

endinterface : OTP_readout_register_OTP_READ_VALUE_if

// OTP_READ_STATUS
interface OTP_readout_register_OTP_READ_STATUS_if;
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

endinterface : OTP_readout_register_OTP_READ_STATUS_if



/*###   OTP_READ_ADDRESS   ######################################################*/
module OTP_readout_register_OTP_READ_ADDRESS #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   OTP_readout_register_OTP_READ_ADDRESS_if.master OTP_readout_register_OTP_READ_ADDRESS);

   // OTP_READ_ADDRESS : ADDR
   logic[11:0]  ADDR, ADDR_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       ADDR <= 12'b0;
     end
     else begin
       ADDR <= ADDR_nxt;
     end
   end

   always_comb begin
     ADDR_nxt = ADDR;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       ADDR_nxt = data_in[11:0]; 
     end
   end

   assign OTP_readout_register_OTP_READ_ADDRESS.ADDR = ADDR;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {4'd0, ADDR} : '0;

   assign OTP_readout_register_OTP_READ_ADDRESS.value = {4'd0, ADDR};
   assign OTP_readout_register_OTP_READ_ADDRESS.access_rd = ((rd == 1'b1) && (reg_addr[addr_width-1:0] == addr )) ? 1'b1 : 1'b0;
   assign OTP_readout_register_OTP_READ_ADDRESS.access_wr = ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) ? 1'b1 : 1'b0;

endmodule : OTP_readout_register_OTP_READ_ADDRESS

/*###   OTP_READ_VALUE   ######################################################*/
module OTP_readout_register_OTP_READ_VALUE #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic           rd,
   output logic[15:0]     data_out,
   OTP_readout_register_OTP_READ_VALUE_if.master OTP_readout_register_OTP_READ_VALUE);

   // OTP_READ_VALUE : ECC
   logic[3:0]  ECC, ECC_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       ECC <= 4'b0;
     end
     else begin
       ECC <= ECC_nxt;
     end
   end

   always_comb begin
     ECC_nxt = ECC;
     if (OTP_readout_register_OTP_READ_VALUE.ECC_set == 1'b1) begin
       ECC_nxt = OTP_readout_register_OTP_READ_VALUE.ECC_in;
     end
   end

   assign OTP_readout_register_OTP_READ_VALUE.ECC = ECC;

   `ifdef VCS

     property ECC_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (OTP_readout_register_OTP_READ_VALUE.ECC_set !== 1'bx);
     endproperty
      as_ECC_set_not_x : assert property (ECC_set_not_x) else $error("OTP_readout_register_OTP_READ_VALUE.ECC_set is x after reset");
     cov_ECC_set_not_x :  cover property (ECC_set_not_x);

   `endif

   // OTP_READ_VALUE : VALUE
   logic[7:0]  VALUE, VALUE_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       VALUE <= 8'b0;
     end
     else begin
       VALUE <= VALUE_nxt;
     end
   end

   always_comb begin
     VALUE_nxt = VALUE;
     if (OTP_readout_register_OTP_READ_VALUE.VALUE_set == 1'b1) begin
       VALUE_nxt = OTP_readout_register_OTP_READ_VALUE.VALUE_in;
     end
   end

   assign OTP_readout_register_OTP_READ_VALUE.VALUE = VALUE;

   `ifdef VCS

     property VALUE_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (OTP_readout_register_OTP_READ_VALUE.VALUE_set !== 1'bx);
     endproperty
      as_VALUE_set_not_x : assert property (VALUE_set_not_x) else $error("OTP_readout_register_OTP_READ_VALUE.VALUE_set is x after reset");
     cov_VALUE_set_not_x :  cover property (VALUE_set_not_x);

   `endif

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {4'd0, ECC, VALUE} : '0;

   assign OTP_readout_register_OTP_READ_VALUE.value = {4'd0, ECC, VALUE};

endmodule : OTP_readout_register_OTP_READ_VALUE

/*###   OTP_READ_STATUS   ######################################################*/
module OTP_readout_register_OTP_READ_STATUS #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic           rd,
   output logic[15:0]     data_out,
   OTP_readout_register_OTP_READ_STATUS_if.master OTP_readout_register_OTP_READ_STATUS);

   // OTP_READ_STATUS : STATUS
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
     if (OTP_readout_register_OTP_READ_STATUS.STATUS_set == 1'b1) begin
       STATUS_nxt = OTP_readout_register_OTP_READ_STATUS.STATUS_in;
     end
   end

   assign OTP_readout_register_OTP_READ_STATUS.STATUS = STATUS;

   `ifdef VCS

     property STATUS_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (OTP_readout_register_OTP_READ_STATUS.STATUS_set !== 1'bx);
     endproperty
      as_STATUS_set_not_x : assert property (STATUS_set_not_x) else $error("OTP_readout_register_OTP_READ_STATUS.STATUS_set is x after reset");
     cov_STATUS_set_not_x :  cover property (STATUS_set_not_x);

   `endif

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {14'd0, STATUS} : '0;

   assign OTP_readout_register_OTP_READ_STATUS.value = {14'd0, STATUS};

endmodule : OTP_readout_register_OTP_READ_STATUS

/*###   Registers   ######################################################*/
module OTP_readout_register #(
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
   OTP_readout_register_OTP_READ_ADDRESS_if.master OTP_readout_register_OTP_READ_ADDRESS,
   OTP_readout_register_OTP_READ_VALUE_if.master OTP_readout_register_OTP_READ_VALUE,
   OTP_readout_register_OTP_READ_STATUS_if.master OTP_readout_register_OTP_READ_STATUS
);

   logic[15:0] data_out_OTP_READ_ADDRESS, data_out_OTP_READ_VALUE, data_out_OTP_READ_STATUS;

   OTP_readout_register_OTP_READ_ADDRESS #( .reg_addr (base_addr + 'h70), .addr_width(addr_width) ) i_OTP_readout_register_OTP_READ_ADDRESS ( .data_out (data_out_OTP_READ_ADDRESS), .*);
   OTP_readout_register_OTP_READ_VALUE #( .reg_addr (base_addr + 'h71), .addr_width(addr_width) ) i_OTP_readout_register_OTP_READ_VALUE ( .data_out (data_out_OTP_READ_VALUE), .*);
   OTP_readout_register_OTP_READ_STATUS #( .reg_addr (base_addr + 'h72), .addr_width(addr_width) ) i_OTP_readout_register_OTP_READ_STATUS ( .data_out (data_out_OTP_READ_STATUS), .*);

   // output data assignment
   assign data_out = data_out_OTP_READ_ADDRESS | data_out_OTP_READ_VALUE | data_out_OTP_READ_STATUS;

endmodule : OTP_readout_register
