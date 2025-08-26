/* ###   interfaces   ###################################################### */

// SCAN
interface scan_registers_SCAN_if;
  logic[15:0] value;
  logic DISABLE_OSC, DISABLE_OSC_in;
  logic VDD_DIS, VDD_DIS_in;
  logic VDD_ILOAD_DIS, VDD_ILOAD_DIS_in;
  logic COMPRESSION, COMPRESSION_in;
  logic VDD_RDIV_DIS, VDD_RDIV_DIS_in;
  logic SCAN, SCAN_in;
  logic DISABLE_OSC_set, VDD_DIS_set, VDD_ILOAD_DIS_set, COMPRESSION_set, VDD_RDIV_DIS_set, SCAN_set;

  modport master (
    input DISABLE_OSC_in, VDD_DIS_in, VDD_ILOAD_DIS_in, COMPRESSION_in, VDD_RDIV_DIS_in, SCAN_in, DISABLE_OSC_set, VDD_DIS_set, VDD_ILOAD_DIS_set, COMPRESSION_set, VDD_RDIV_DIS_set, SCAN_set, 
    output value, DISABLE_OSC, VDD_DIS, VDD_ILOAD_DIS, COMPRESSION, VDD_RDIV_DIS, SCAN
  );

  modport slave (
    input value, DISABLE_OSC, VDD_DIS, VDD_ILOAD_DIS, COMPRESSION, VDD_RDIV_DIS, SCAN, 
    output DISABLE_OSC_in, VDD_DIS_in, VDD_ILOAD_DIS_in, COMPRESSION_in, VDD_RDIV_DIS_in, SCAN_in, DISABLE_OSC_set, VDD_DIS_set, VDD_ILOAD_DIS_set, COMPRESSION_set, VDD_RDIV_DIS_set, SCAN_set
  );

endinterface : scan_registers_SCAN_if



/*###   SCAN   ######################################################*/
module scan_registers_SCAN #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   scan_registers_SCAN_if.master scan_registers_SCAN);

   // SCAN : DISABLE_OSC
   logic  DISABLE_OSC, DISABLE_OSC_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DISABLE_OSC <= 1'b0;
     end
     else begin
       DISABLE_OSC <= DISABLE_OSC_nxt;
     end
   end

   always_comb begin
     DISABLE_OSC_nxt = DISABLE_OSC;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       DISABLE_OSC_nxt = data_in[5:5]; 
     end
     if (scan_registers_SCAN.DISABLE_OSC_set == 1'b1) begin
       DISABLE_OSC_nxt = scan_registers_SCAN.DISABLE_OSC_in;
     end
   end

   assign scan_registers_SCAN.DISABLE_OSC = DISABLE_OSC;

   `ifdef VCS

     property DISABLE_OSC_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (scan_registers_SCAN.DISABLE_OSC_set !== 1'bx);
     endproperty
      as_DISABLE_OSC_set_not_x : assert property (DISABLE_OSC_set_not_x) else $error("scan_registers_SCAN.DISABLE_OSC_set is x after reset");
     cov_DISABLE_OSC_set_not_x :  cover property (DISABLE_OSC_set_not_x);

   `endif

   // SCAN : VDD_DIS
   logic  VDD_DIS, VDD_DIS_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       VDD_DIS <= 1'b0;
     end
     else begin
       VDD_DIS <= VDD_DIS_nxt;
     end
   end

   always_comb begin
     VDD_DIS_nxt = VDD_DIS;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       VDD_DIS_nxt = data_in[4:4]; 
     end
     if (scan_registers_SCAN.VDD_DIS_set == 1'b1) begin
       VDD_DIS_nxt = scan_registers_SCAN.VDD_DIS_in;
     end
   end

   assign scan_registers_SCAN.VDD_DIS = VDD_DIS;

   `ifdef VCS

     property VDD_DIS_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (scan_registers_SCAN.VDD_DIS_set !== 1'bx);
     endproperty
      as_VDD_DIS_set_not_x : assert property (VDD_DIS_set_not_x) else $error("scan_registers_SCAN.VDD_DIS_set is x after reset");
     cov_VDD_DIS_set_not_x :  cover property (VDD_DIS_set_not_x);

   `endif

   // SCAN : VDD_ILOAD_DIS
   logic  VDD_ILOAD_DIS, VDD_ILOAD_DIS_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       VDD_ILOAD_DIS <= 1'b0;
     end
     else begin
       VDD_ILOAD_DIS <= VDD_ILOAD_DIS_nxt;
     end
   end

   always_comb begin
     VDD_ILOAD_DIS_nxt = VDD_ILOAD_DIS;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       VDD_ILOAD_DIS_nxt = data_in[3:3]; 
     end
     if (scan_registers_SCAN.VDD_ILOAD_DIS_set == 1'b1) begin
       VDD_ILOAD_DIS_nxt = scan_registers_SCAN.VDD_ILOAD_DIS_in;
     end
   end

   assign scan_registers_SCAN.VDD_ILOAD_DIS = VDD_ILOAD_DIS;

   `ifdef VCS

     property VDD_ILOAD_DIS_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (scan_registers_SCAN.VDD_ILOAD_DIS_set !== 1'bx);
     endproperty
      as_VDD_ILOAD_DIS_set_not_x : assert property (VDD_ILOAD_DIS_set_not_x) else $error("scan_registers_SCAN.VDD_ILOAD_DIS_set is x after reset");
     cov_VDD_ILOAD_DIS_set_not_x :  cover property (VDD_ILOAD_DIS_set_not_x);

   `endif

   // SCAN : COMPRESSION
   logic  COMPRESSION, COMPRESSION_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       COMPRESSION <= 1'b0;
     end
     else begin
       COMPRESSION <= COMPRESSION_nxt;
     end
   end

   always_comb begin
     COMPRESSION_nxt = COMPRESSION;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       COMPRESSION_nxt = data_in[2:2]; 
     end
     if (scan_registers_SCAN.COMPRESSION_set == 1'b1) begin
       COMPRESSION_nxt = scan_registers_SCAN.COMPRESSION_in;
     end
   end

   assign scan_registers_SCAN.COMPRESSION = COMPRESSION;

   `ifdef VCS

     property COMPRESSION_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (scan_registers_SCAN.COMPRESSION_set !== 1'bx);
     endproperty
      as_COMPRESSION_set_not_x : assert property (COMPRESSION_set_not_x) else $error("scan_registers_SCAN.COMPRESSION_set is x after reset");
     cov_COMPRESSION_set_not_x :  cover property (COMPRESSION_set_not_x);

   `endif

   // SCAN : VDD_RDIV_DIS
   logic  VDD_RDIV_DIS, VDD_RDIV_DIS_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       VDD_RDIV_DIS <= 1'b0;
     end
     else begin
       VDD_RDIV_DIS <= VDD_RDIV_DIS_nxt;
     end
   end

   always_comb begin
     VDD_RDIV_DIS_nxt = VDD_RDIV_DIS;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       VDD_RDIV_DIS_nxt = data_in[1:1]; 
     end
     if (scan_registers_SCAN.VDD_RDIV_DIS_set == 1'b1) begin
       VDD_RDIV_DIS_nxt = scan_registers_SCAN.VDD_RDIV_DIS_in;
     end
   end

   assign scan_registers_SCAN.VDD_RDIV_DIS = VDD_RDIV_DIS;

   `ifdef VCS

     property VDD_RDIV_DIS_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (scan_registers_SCAN.VDD_RDIV_DIS_set !== 1'bx);
     endproperty
      as_VDD_RDIV_DIS_set_not_x : assert property (VDD_RDIV_DIS_set_not_x) else $error("scan_registers_SCAN.VDD_RDIV_DIS_set is x after reset");
     cov_VDD_RDIV_DIS_set_not_x :  cover property (VDD_RDIV_DIS_set_not_x);

   `endif

   // SCAN : SCAN
   logic  SCAN, SCAN_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       SCAN <= 1'b0;
     end
     else begin
       SCAN <= SCAN_nxt;
     end
   end

   always_comb begin
     SCAN_nxt = SCAN;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && (data_in[0] == 1'b1)) begin
       SCAN_nxt = 1'b1; 
     end
     if (scan_registers_SCAN.SCAN_set == 1'b1) begin
       SCAN_nxt = scan_registers_SCAN.SCAN_in;
     end
   end

   assign scan_registers_SCAN.SCAN = SCAN;

   `ifdef VCS

     property SCAN_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (scan_registers_SCAN.SCAN_set !== 1'bx);
     endproperty
      as_SCAN_set_not_x : assert property (SCAN_set_not_x) else $error("scan_registers_SCAN.SCAN_set is x after reset");
     cov_SCAN_set_not_x :  cover property (SCAN_set_not_x);

   `endif

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {10'd0, DISABLE_OSC, VDD_DIS, VDD_ILOAD_DIS, COMPRESSION, VDD_RDIV_DIS, SCAN} : '0;

   assign scan_registers_SCAN.value = {10'd0, DISABLE_OSC, VDD_DIS, VDD_ILOAD_DIS, COMPRESSION, VDD_RDIV_DIS, SCAN};

endmodule : scan_registers_SCAN

/*###   Registers   ######################################################*/
module scan_registers #(
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
   scan_registers_SCAN_if.master scan_registers_SCAN
);

   logic[15:0] data_out_SCAN;

   scan_registers_SCAN #( .reg_addr (base_addr + 'h0), .addr_width(addr_width) ) i_scan_registers_SCAN ( .data_out (data_out_SCAN), .*);

   // output data assignment
   assign data_out = data_out_SCAN;

endmodule : scan_registers
