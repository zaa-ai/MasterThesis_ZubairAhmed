/* ###   interfaces   ###################################################### */

// IR_ELIP_RDF
interface ELIP_test_register_IR_ELIP_RDF_if;
  logic[31:0] value;
  logic[15:0] ADDR, ADDR_in;
  logic[15:0] DATA, DATA_in;
  logic ADDR_set, DATA_set;

  modport master (
    input ADDR_in, DATA_in, ADDR_set, DATA_set, 
    output value, ADDR, DATA
  );

  modport slave (
    input value, ADDR, DATA, 
    output ADDR_in, DATA_in, ADDR_set, DATA_set
  );

endinterface : ELIP_test_register_IR_ELIP_RDF_if

// IR_ELIP_RD
interface ELIP_test_register_IR_ELIP_RD_if;
  logic[31:0] value;
  logic[15:0] DATA, DATA_in;
  logic DATA_set;

  modport master (
    input DATA_in, DATA_set, 
    output value, DATA
  );

  modport slave (
    input value, DATA, 
    output DATA_in, DATA_set
  );

endinterface : ELIP_test_register_IR_ELIP_RD_if

// IR_ELIP_RDI
interface ELIP_test_register_IR_ELIP_RDI_if;
  logic[31:0] value;
  logic[15:0] DATA, DATA_in;
  logic DATA_set;

  modport master (
    input DATA_in, DATA_set, 
    output value, DATA
  );

  modport slave (
    input value, DATA, 
    output DATA_in, DATA_set
  );

endinterface : ELIP_test_register_IR_ELIP_RDI_if

// IR_ELIP_WRF
interface ELIP_test_register_IR_ELIP_WRF_if;
  logic[31:0] value;
  logic[15:0] ADDR, ADDR_in;
  logic[15:0] DATA, DATA_in;
  logic ADDR_set, DATA_set;

  modport master (
    input ADDR_in, DATA_in, ADDR_set, DATA_set, 
    output value, ADDR, DATA
  );

  modport slave (
    input value, ADDR, DATA, 
    output ADDR_in, DATA_in, ADDR_set, DATA_set
  );

endinterface : ELIP_test_register_IR_ELIP_WRF_if

// IR_ELIP_WR
interface ELIP_test_register_IR_ELIP_WR_if;
  logic[31:0] value;
  logic[15:0] DATA, DATA_in;
  logic DATA_set;

  modport master (
    input DATA_in, DATA_set, 
    output value, DATA
  );

  modport slave (
    input value, DATA, 
    output DATA_in, DATA_set
  );

endinterface : ELIP_test_register_IR_ELIP_WR_if

// IR_ELIP_WRI
interface ELIP_test_register_IR_ELIP_WRI_if;
  logic[31:0] value;
  logic[15:0] IR_ELIP_WRI, IR_ELIP_WRI_in;
  logic IR_ELIP_WRI_set;

  modport master (
    input IR_ELIP_WRI_in, IR_ELIP_WRI_set, 
    output value, IR_ELIP_WRI
  );

  modport slave (
    input value, IR_ELIP_WRI, 
    output IR_ELIP_WRI_in, IR_ELIP_WRI_set
  );

endinterface : ELIP_test_register_IR_ELIP_WRI_if



/*###   IR_ELIP_RDF   ######################################################*/
module ELIP_test_register_IR_ELIP_RDF #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[31:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[31:0]     data_out,
   ELIP_test_register_IR_ELIP_RDF_if.master ELIP_test_register_IR_ELIP_RDF);

   // IR_ELIP_RDF : ADDR
   logic[15:0]  ADDR, ADDR_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       ADDR <= 16'b0;
     end
     else begin
       ADDR <= ADDR_nxt;
     end
   end

   always_comb begin
     ADDR_nxt = ADDR;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       ADDR_nxt = data_in[31:16]; 
     end
     if (ELIP_test_register_IR_ELIP_RDF.ADDR_set == 1'b1) begin
       ADDR_nxt = ELIP_test_register_IR_ELIP_RDF.ADDR_in;
     end
   end

   assign ELIP_test_register_IR_ELIP_RDF.ADDR = ADDR;

   `ifdef VCS

     property ADDR_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (ELIP_test_register_IR_ELIP_RDF.ADDR_set !== 1'bx);
     endproperty
      as_ADDR_set_not_x : assert property (ADDR_set_not_x) else $error("ELIP_test_register_IR_ELIP_RDF.ADDR_set is x after reset");
     cov_ADDR_set_not_x :  cover property (ADDR_set_not_x);

   `endif

   // IR_ELIP_RDF : DATA
   logic[15:0]  DATA, DATA_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DATA <= 16'b0;
     end
     else begin
       DATA <= DATA_nxt;
     end
   end

   always_comb begin
     DATA_nxt = DATA;
     if (ELIP_test_register_IR_ELIP_RDF.DATA_set == 1'b1) begin
       DATA_nxt = ELIP_test_register_IR_ELIP_RDF.DATA_in;
     end
   end

   assign ELIP_test_register_IR_ELIP_RDF.DATA = DATA;

   `ifdef VCS

     property DATA_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (ELIP_test_register_IR_ELIP_RDF.DATA_set !== 1'bx);
     endproperty
      as_DATA_set_not_x : assert property (DATA_set_not_x) else $error("ELIP_test_register_IR_ELIP_RDF.DATA_set is x after reset");
     cov_DATA_set_not_x :  cover property (DATA_set_not_x);

   `endif

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {16'd0, DATA} : '0;

   assign ELIP_test_register_IR_ELIP_RDF.value = {ADDR, DATA};

endmodule : ELIP_test_register_IR_ELIP_RDF

/*###   IR_ELIP_RD   ######################################################*/
module ELIP_test_register_IR_ELIP_RD #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic           rd,
   output logic[31:0]     data_out,
   ELIP_test_register_IR_ELIP_RD_if.master ELIP_test_register_IR_ELIP_RD);

   // IR_ELIP_RD : DATA
   logic[15:0]  DATA, DATA_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DATA <= 16'b0;
     end
     else begin
       DATA <= DATA_nxt;
     end
   end

   always_comb begin
     DATA_nxt = DATA;
     if (ELIP_test_register_IR_ELIP_RD.DATA_set == 1'b1) begin
       DATA_nxt = ELIP_test_register_IR_ELIP_RD.DATA_in;
     end
   end

   assign ELIP_test_register_IR_ELIP_RD.DATA = DATA;

   `ifdef VCS

     property DATA_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (ELIP_test_register_IR_ELIP_RD.DATA_set !== 1'bx);
     endproperty
      as_DATA_set_not_x : assert property (DATA_set_not_x) else $error("ELIP_test_register_IR_ELIP_RD.DATA_set is x after reset");
     cov_DATA_set_not_x :  cover property (DATA_set_not_x);

   `endif

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {16'd0, DATA} : '0;

   assign ELIP_test_register_IR_ELIP_RD.value = {16'd0, DATA};

endmodule : ELIP_test_register_IR_ELIP_RD

/*###   IR_ELIP_RDI   ######################################################*/
module ELIP_test_register_IR_ELIP_RDI #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic           rd,
   output logic[31:0]     data_out,
   ELIP_test_register_IR_ELIP_RDI_if.master ELIP_test_register_IR_ELIP_RDI);

   // IR_ELIP_RDI : DATA
   logic[15:0]  DATA, DATA_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DATA <= 16'b0;
     end
     else begin
       DATA <= DATA_nxt;
     end
   end

   always_comb begin
     DATA_nxt = DATA;
     if (ELIP_test_register_IR_ELIP_RDI.DATA_set == 1'b1) begin
       DATA_nxt = ELIP_test_register_IR_ELIP_RDI.DATA_in;
     end
   end

   assign ELIP_test_register_IR_ELIP_RDI.DATA = DATA;

   `ifdef VCS

     property DATA_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (ELIP_test_register_IR_ELIP_RDI.DATA_set !== 1'bx);
     endproperty
      as_DATA_set_not_x : assert property (DATA_set_not_x) else $error("ELIP_test_register_IR_ELIP_RDI.DATA_set is x after reset");
     cov_DATA_set_not_x :  cover property (DATA_set_not_x);

   `endif

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {16'd0, DATA} : '0;

   assign ELIP_test_register_IR_ELIP_RDI.value = {16'd0, DATA};

endmodule : ELIP_test_register_IR_ELIP_RDI

/*###   IR_ELIP_WRF   ######################################################*/
module ELIP_test_register_IR_ELIP_WRF #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[31:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[31:0]     data_out,
   ELIP_test_register_IR_ELIP_WRF_if.master ELIP_test_register_IR_ELIP_WRF);

   // IR_ELIP_WRF : ADDR
   logic[15:0]  ADDR, ADDR_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       ADDR <= 16'b0;
     end
     else begin
       ADDR <= ADDR_nxt;
     end
   end

   always_comb begin
     ADDR_nxt = ADDR;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       ADDR_nxt = data_in[31:16]; 
     end
     if (ELIP_test_register_IR_ELIP_WRF.ADDR_set == 1'b1) begin
       ADDR_nxt = ELIP_test_register_IR_ELIP_WRF.ADDR_in;
     end
   end

   assign ELIP_test_register_IR_ELIP_WRF.ADDR = ADDR;

   `ifdef VCS

     property ADDR_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (ELIP_test_register_IR_ELIP_WRF.ADDR_set !== 1'bx);
     endproperty
      as_ADDR_set_not_x : assert property (ADDR_set_not_x) else $error("ELIP_test_register_IR_ELIP_WRF.ADDR_set is x after reset");
     cov_ADDR_set_not_x :  cover property (ADDR_set_not_x);

   `endif

   // IR_ELIP_WRF : DATA
   logic[15:0]  DATA, DATA_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DATA <= 16'b0;
     end
     else begin
       DATA <= DATA_nxt;
     end
   end

   always_comb begin
     DATA_nxt = DATA;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       DATA_nxt = data_in[15:0]; 
     end
     if (ELIP_test_register_IR_ELIP_WRF.DATA_set == 1'b1) begin
       DATA_nxt = ELIP_test_register_IR_ELIP_WRF.DATA_in;
     end
   end

   assign ELIP_test_register_IR_ELIP_WRF.DATA = DATA;

   `ifdef VCS

     property DATA_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (ELIP_test_register_IR_ELIP_WRF.DATA_set !== 1'bx);
     endproperty
      as_DATA_set_not_x : assert property (DATA_set_not_x) else $error("ELIP_test_register_IR_ELIP_WRF.DATA_set is x after reset");
     cov_DATA_set_not_x :  cover property (DATA_set_not_x);

   `endif

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {16'd0, 16'd0} : '0;

   assign ELIP_test_register_IR_ELIP_WRF.value = {ADDR, DATA};

endmodule : ELIP_test_register_IR_ELIP_WRF

/*###   IR_ELIP_WR   ######################################################*/
module ELIP_test_register_IR_ELIP_WR #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic           rd,
   output logic[31:0]     data_out,
   ELIP_test_register_IR_ELIP_WR_if.master ELIP_test_register_IR_ELIP_WR);

   // IR_ELIP_WR : DATA
   logic[15:0]  DATA, DATA_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DATA <= 16'b0;
     end
     else begin
       DATA <= DATA_nxt;
     end
   end

   always_comb begin
     DATA_nxt = DATA;
     if (ELIP_test_register_IR_ELIP_WR.DATA_set == 1'b1) begin
       DATA_nxt = ELIP_test_register_IR_ELIP_WR.DATA_in;
     end
   end

   assign ELIP_test_register_IR_ELIP_WR.DATA = DATA;

   `ifdef VCS

     property DATA_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (ELIP_test_register_IR_ELIP_WR.DATA_set !== 1'bx);
     endproperty
      as_DATA_set_not_x : assert property (DATA_set_not_x) else $error("ELIP_test_register_IR_ELIP_WR.DATA_set is x after reset");
     cov_DATA_set_not_x :  cover property (DATA_set_not_x);

   `endif

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {16'd0, DATA} : '0;

   assign ELIP_test_register_IR_ELIP_WR.value = {16'd0, DATA};

endmodule : ELIP_test_register_IR_ELIP_WR

/*###   IR_ELIP_WRI   ######################################################*/
module ELIP_test_register_IR_ELIP_WRI #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[31:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[31:0]     data_out,
   ELIP_test_register_IR_ELIP_WRI_if.master ELIP_test_register_IR_ELIP_WRI);

   // IR_ELIP_WRI : IR_ELIP_WRI
   logic[15:0]  IR_ELIP_WRI, IR_ELIP_WRI_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       IR_ELIP_WRI <= 16'b0;
     end
     else begin
       IR_ELIP_WRI <= IR_ELIP_WRI_nxt;
     end
   end

   always_comb begin
     IR_ELIP_WRI_nxt = IR_ELIP_WRI;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       IR_ELIP_WRI_nxt = data_in[15:0]; 
     end
     if (ELIP_test_register_IR_ELIP_WRI.IR_ELIP_WRI_set == 1'b1) begin
       IR_ELIP_WRI_nxt = ELIP_test_register_IR_ELIP_WRI.IR_ELIP_WRI_in;
     end
   end

   assign ELIP_test_register_IR_ELIP_WRI.IR_ELIP_WRI = IR_ELIP_WRI;

   `ifdef VCS

     property IR_ELIP_WRI_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (ELIP_test_register_IR_ELIP_WRI.IR_ELIP_WRI_set !== 1'bx);
     endproperty
      as_IR_ELIP_WRI_set_not_x : assert property (IR_ELIP_WRI_set_not_x) else $error("ELIP_test_register_IR_ELIP_WRI.IR_ELIP_WRI_set is x after reset");
     cov_IR_ELIP_WRI_set_not_x :  cover property (IR_ELIP_WRI_set_not_x);

   `endif

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {16'd0, IR_ELIP_WRI} : '0;

   assign ELIP_test_register_IR_ELIP_WRI.value = {16'd0, IR_ELIP_WRI};

endmodule : ELIP_test_register_IR_ELIP_WRI

/*###   Registers   ######################################################*/
module ELIP_test_register #(
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
   ELIP_test_register_IR_ELIP_RDF_if.master ELIP_test_register_IR_ELIP_RDF,
   ELIP_test_register_IR_ELIP_RD_if.master ELIP_test_register_IR_ELIP_RD,
   ELIP_test_register_IR_ELIP_RDI_if.master ELIP_test_register_IR_ELIP_RDI,
   ELIP_test_register_IR_ELIP_WRF_if.master ELIP_test_register_IR_ELIP_WRF,
   ELIP_test_register_IR_ELIP_WR_if.master ELIP_test_register_IR_ELIP_WR,
   ELIP_test_register_IR_ELIP_WRI_if.master ELIP_test_register_IR_ELIP_WRI
);

   logic[31:0] data_out_IR_ELIP_RDF, data_out_IR_ELIP_RD, data_out_IR_ELIP_RDI, data_out_IR_ELIP_WRF, data_out_IR_ELIP_WR, data_out_IR_ELIP_WRI;

   ELIP_test_register_IR_ELIP_RDF #( .reg_addr (base_addr + 'hc0), .addr_width(addr_width) ) i_ELIP_test_register_IR_ELIP_RDF ( .data_out (data_out_IR_ELIP_RDF), .*);
   ELIP_test_register_IR_ELIP_RD #( .reg_addr (base_addr + 'hc1), .addr_width(addr_width) ) i_ELIP_test_register_IR_ELIP_RD ( .data_out (data_out_IR_ELIP_RD), .*);
   ELIP_test_register_IR_ELIP_RDI #( .reg_addr (base_addr + 'hc2), .addr_width(addr_width) ) i_ELIP_test_register_IR_ELIP_RDI ( .data_out (data_out_IR_ELIP_RDI), .*);
   ELIP_test_register_IR_ELIP_WRF #( .reg_addr (base_addr + 'hc3), .addr_width(addr_width) ) i_ELIP_test_register_IR_ELIP_WRF ( .data_out (data_out_IR_ELIP_WRF), .*);
   ELIP_test_register_IR_ELIP_WR #( .reg_addr (base_addr + 'hc4), .addr_width(addr_width) ) i_ELIP_test_register_IR_ELIP_WR ( .data_out (data_out_IR_ELIP_WR), .*);
   ELIP_test_register_IR_ELIP_WRI #( .reg_addr (base_addr + 'hc5), .addr_width(addr_width) ) i_ELIP_test_register_IR_ELIP_WRI ( .data_out (data_out_IR_ELIP_WRI), .*);

   // output data assignment
   assign data_out = data_out_IR_ELIP_RDF | data_out_IR_ELIP_RD | data_out_IR_ELIP_RDI | data_out_IR_ELIP_WRF | data_out_IR_ELIP_WR | data_out_IR_ELIP_WRI;

endmodule : ELIP_test_register
