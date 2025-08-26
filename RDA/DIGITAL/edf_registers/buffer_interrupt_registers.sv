/* ###   interfaces   ###################################################### */

// BUF_IRQ_STAT
interface buffer_interrupt_registers_BUF_IRQ_STAT_if;
  logic[15:0] value;
  logic SPI_CMD_FE, SPI_CMD_FE_in;
  logic[1:0] DSI_CMD_FE, DSI_CMD_FE_in;
  logic[1:0] DSI_PDCM_FE, DSI_PDCM_FE_in;
  logic[1:0] DSI_CRM_FE, DSI_CRM_FE_in;
  logic SPI_CMD_FE_set, DSI_CMD_FE_set, DSI_PDCM_FE_set, DSI_CRM_FE_set;

  modport master (
    input SPI_CMD_FE_in, DSI_CMD_FE_in, DSI_PDCM_FE_in, DSI_CRM_FE_in, SPI_CMD_FE_set, DSI_CMD_FE_set, DSI_PDCM_FE_set, DSI_CRM_FE_set, 
    output value, SPI_CMD_FE, DSI_CMD_FE, DSI_PDCM_FE, DSI_CRM_FE
  );

  modport slave (
    input value, SPI_CMD_FE, DSI_CMD_FE, DSI_PDCM_FE, DSI_CRM_FE, 
    output SPI_CMD_FE_in, DSI_CMD_FE_in, DSI_PDCM_FE_in, DSI_CRM_FE_in, SPI_CMD_FE_set, DSI_CMD_FE_set, DSI_PDCM_FE_set, DSI_CRM_FE_set
  );

endinterface : buffer_interrupt_registers_BUF_IRQ_STAT_if

// BUF_IRQ_MASK
interface buffer_interrupt_registers_BUF_IRQ_MASK_if;
  logic[15:0] value;
  logic SPI_CMD_FE;
  logic[1:0] DSI_CMD_FE;
  logic[1:0] DSI_PDCM_FE;
  logic[1:0] DSI_CRM_FE;

  modport master (
    output value, SPI_CMD_FE, DSI_CMD_FE, DSI_PDCM_FE, DSI_CRM_FE
  );

  modport slave (
    input value, SPI_CMD_FE, DSI_CMD_FE, DSI_PDCM_FE, DSI_CRM_FE
  );

endinterface : buffer_interrupt_registers_BUF_IRQ_MASK_if

// BUF_FILL_WARN
interface buffer_interrupt_registers_BUF_FILL_WARN_if;
  logic[15:0] value;
  logic SPI_CMD_FW, SPI_CMD_FW_in;
  logic[1:0] DSI_CMD_FW, DSI_CMD_FW_in;
  logic[1:0] DSI_PDCM_FW, DSI_PDCM_FW_in;
  logic[1:0] DSI_CRM_FW, DSI_CRM_FW_in;

  modport master (
    input SPI_CMD_FW_in, DSI_CMD_FW_in, DSI_PDCM_FW_in, DSI_CRM_FW_in, 
    output value, SPI_CMD_FW, DSI_CMD_FW, DSI_PDCM_FW, DSI_CRM_FW
  );

  modport slave (
    input value, SPI_CMD_FW, DSI_CMD_FW, DSI_PDCM_FW, DSI_CRM_FW, 
    output SPI_CMD_FW_in, DSI_CMD_FW_in, DSI_PDCM_FW_in, DSI_CRM_FW_in
  );

endinterface : buffer_interrupt_registers_BUF_FILL_WARN_if



/*###   BUF_IRQ_STAT   ######################################################*/
module buffer_interrupt_registers_BUF_IRQ_STAT #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   buffer_interrupt_registers_BUF_IRQ_STAT_if.master buffer_interrupt_registers_BUF_IRQ_STAT);

   // BUF_IRQ_STAT : SPI_CMD_FE
   logic  SPI_CMD_FE, SPI_CMD_FE_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       SPI_CMD_FE <= 1'b0;
     end
     else begin
       SPI_CMD_FE <= SPI_CMD_FE_nxt;
     end
   end

   always_comb begin
     SPI_CMD_FE_nxt = SPI_CMD_FE;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[6])) begin
       SPI_CMD_FE_nxt = SPI_CMD_FE & (~data_in[6]);
     end
     if (buffer_interrupt_registers_BUF_IRQ_STAT.SPI_CMD_FE_set == 1'b1) begin
       SPI_CMD_FE_nxt = buffer_interrupt_registers_BUF_IRQ_STAT.SPI_CMD_FE_in;
     end
   end

   assign buffer_interrupt_registers_BUF_IRQ_STAT.SPI_CMD_FE = SPI_CMD_FE;

   `ifdef VCS

     property SPI_CMD_FE_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (buffer_interrupt_registers_BUF_IRQ_STAT.SPI_CMD_FE_set !== 1'bx);
     endproperty
      as_SPI_CMD_FE_set_not_x : assert property (SPI_CMD_FE_set_not_x) else $error("buffer_interrupt_registers_BUF_IRQ_STAT.SPI_CMD_FE_set is x after reset");
     cov_SPI_CMD_FE_set_not_x :  cover property (SPI_CMD_FE_set_not_x);

   `endif

   // BUF_IRQ_STAT : DSI_CMD_FE
   logic[1:0]  DSI_CMD_FE, DSI_CMD_FE_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DSI_CMD_FE <= 2'b0;
     end
     else begin
       DSI_CMD_FE <= DSI_CMD_FE_nxt;
     end
   end

   always_comb begin
     DSI_CMD_FE_nxt = DSI_CMD_FE;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[5:4])) begin
       DSI_CMD_FE_nxt = DSI_CMD_FE & (~data_in[5:4]);
     end
     if (buffer_interrupt_registers_BUF_IRQ_STAT.DSI_CMD_FE_set == 1'b1) begin
       DSI_CMD_FE_nxt = buffer_interrupt_registers_BUF_IRQ_STAT.DSI_CMD_FE_in;
     end
   end

   assign buffer_interrupt_registers_BUF_IRQ_STAT.DSI_CMD_FE = DSI_CMD_FE;

   `ifdef VCS

     property DSI_CMD_FE_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (buffer_interrupt_registers_BUF_IRQ_STAT.DSI_CMD_FE_set !== 1'bx);
     endproperty
      as_DSI_CMD_FE_set_not_x : assert property (DSI_CMD_FE_set_not_x) else $error("buffer_interrupt_registers_BUF_IRQ_STAT.DSI_CMD_FE_set is x after reset");
     cov_DSI_CMD_FE_set_not_x :  cover property (DSI_CMD_FE_set_not_x);

   `endif

   // BUF_IRQ_STAT : DSI_PDCM_FE
   logic[1:0]  DSI_PDCM_FE, DSI_PDCM_FE_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DSI_PDCM_FE <= 2'b0;
     end
     else begin
       DSI_PDCM_FE <= DSI_PDCM_FE_nxt;
     end
   end

   always_comb begin
     DSI_PDCM_FE_nxt = DSI_PDCM_FE;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[3:2])) begin
       DSI_PDCM_FE_nxt = DSI_PDCM_FE & (~data_in[3:2]);
     end
     if (buffer_interrupt_registers_BUF_IRQ_STAT.DSI_PDCM_FE_set == 1'b1) begin
       DSI_PDCM_FE_nxt = buffer_interrupt_registers_BUF_IRQ_STAT.DSI_PDCM_FE_in;
     end
   end

   assign buffer_interrupt_registers_BUF_IRQ_STAT.DSI_PDCM_FE = DSI_PDCM_FE;

   `ifdef VCS

     property DSI_PDCM_FE_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (buffer_interrupt_registers_BUF_IRQ_STAT.DSI_PDCM_FE_set !== 1'bx);
     endproperty
      as_DSI_PDCM_FE_set_not_x : assert property (DSI_PDCM_FE_set_not_x) else $error("buffer_interrupt_registers_BUF_IRQ_STAT.DSI_PDCM_FE_set is x after reset");
     cov_DSI_PDCM_FE_set_not_x :  cover property (DSI_PDCM_FE_set_not_x);

   `endif

   // BUF_IRQ_STAT : DSI_CRM_FE
   logic[1:0]  DSI_CRM_FE, DSI_CRM_FE_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DSI_CRM_FE <= 2'b0;
     end
     else begin
       DSI_CRM_FE <= DSI_CRM_FE_nxt;
     end
   end

   always_comb begin
     DSI_CRM_FE_nxt = DSI_CRM_FE;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[1:0])) begin
       DSI_CRM_FE_nxt = DSI_CRM_FE & (~data_in[1:0]);
     end
     if (buffer_interrupt_registers_BUF_IRQ_STAT.DSI_CRM_FE_set == 1'b1) begin
       DSI_CRM_FE_nxt = buffer_interrupt_registers_BUF_IRQ_STAT.DSI_CRM_FE_in;
     end
   end

   assign buffer_interrupt_registers_BUF_IRQ_STAT.DSI_CRM_FE = DSI_CRM_FE;

   `ifdef VCS

     property DSI_CRM_FE_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (buffer_interrupt_registers_BUF_IRQ_STAT.DSI_CRM_FE_set !== 1'bx);
     endproperty
      as_DSI_CRM_FE_set_not_x : assert property (DSI_CRM_FE_set_not_x) else $error("buffer_interrupt_registers_BUF_IRQ_STAT.DSI_CRM_FE_set is x after reset");
     cov_DSI_CRM_FE_set_not_x :  cover property (DSI_CRM_FE_set_not_x);

   `endif

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {9'd0, SPI_CMD_FE, DSI_CMD_FE, DSI_PDCM_FE, DSI_CRM_FE} : '0;

   assign buffer_interrupt_registers_BUF_IRQ_STAT.value = {9'd0, SPI_CMD_FE, DSI_CMD_FE, DSI_PDCM_FE, DSI_CRM_FE};

endmodule : buffer_interrupt_registers_BUF_IRQ_STAT

/*###   BUF_IRQ_MASK   ######################################################*/
module buffer_interrupt_registers_BUF_IRQ_MASK #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   buffer_interrupt_registers_BUF_IRQ_MASK_if.master buffer_interrupt_registers_BUF_IRQ_MASK);

   // BUF_IRQ_MASK : SPI_CMD_FE
   logic  SPI_CMD_FE, SPI_CMD_FE_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       SPI_CMD_FE <= 1'b1;
     end
     else begin
       SPI_CMD_FE <= SPI_CMD_FE_nxt;
     end
   end

   always_comb begin
     SPI_CMD_FE_nxt = SPI_CMD_FE;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       SPI_CMD_FE_nxt = data_in[6:6]; 
     end
   end

   assign buffer_interrupt_registers_BUF_IRQ_MASK.SPI_CMD_FE = SPI_CMD_FE;

   // BUF_IRQ_MASK : DSI_CMD_FE
   logic[1:0]  DSI_CMD_FE, DSI_CMD_FE_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DSI_CMD_FE <= 2'b11;
     end
     else begin
       DSI_CMD_FE <= DSI_CMD_FE_nxt;
     end
   end

   always_comb begin
     DSI_CMD_FE_nxt = DSI_CMD_FE;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       DSI_CMD_FE_nxt = data_in[5:4]; 
     end
   end

   assign buffer_interrupt_registers_BUF_IRQ_MASK.DSI_CMD_FE = DSI_CMD_FE;

   // BUF_IRQ_MASK : DSI_PDCM_FE
   logic[1:0]  DSI_PDCM_FE, DSI_PDCM_FE_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DSI_PDCM_FE <= 2'b11;
     end
     else begin
       DSI_PDCM_FE <= DSI_PDCM_FE_nxt;
     end
   end

   always_comb begin
     DSI_PDCM_FE_nxt = DSI_PDCM_FE;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       DSI_PDCM_FE_nxt = data_in[3:2]; 
     end
   end

   assign buffer_interrupt_registers_BUF_IRQ_MASK.DSI_PDCM_FE = DSI_PDCM_FE;

   // BUF_IRQ_MASK : DSI_CRM_FE
   logic[1:0]  DSI_CRM_FE, DSI_CRM_FE_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DSI_CRM_FE <= 2'b11;
     end
     else begin
       DSI_CRM_FE <= DSI_CRM_FE_nxt;
     end
   end

   always_comb begin
     DSI_CRM_FE_nxt = DSI_CRM_FE;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       DSI_CRM_FE_nxt = data_in[1:0]; 
     end
   end

   assign buffer_interrupt_registers_BUF_IRQ_MASK.DSI_CRM_FE = DSI_CRM_FE;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {9'd0, SPI_CMD_FE, DSI_CMD_FE, DSI_PDCM_FE, DSI_CRM_FE} : '0;

   assign buffer_interrupt_registers_BUF_IRQ_MASK.value = {9'd0, SPI_CMD_FE, DSI_CMD_FE, DSI_PDCM_FE, DSI_CRM_FE};

endmodule : buffer_interrupt_registers_BUF_IRQ_MASK

/*###   BUF_FILL_WARN   ######################################################*/
module buffer_interrupt_registers_BUF_FILL_WARN #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   input logic[addr_width-1:0] addr,
   input logic           rd,
   output logic[15:0]     data_out,
   buffer_interrupt_registers_BUF_FILL_WARN_if.master buffer_interrupt_registers_BUF_FILL_WARN);

   // BUF_FILL_WARN : SPI_CMD_FW
   logic  SPI_CMD_FW;


   always_comb begin
       SPI_CMD_FW = buffer_interrupt_registers_BUF_FILL_WARN.SPI_CMD_FW_in;
   end

   assign buffer_interrupt_registers_BUF_FILL_WARN.SPI_CMD_FW = SPI_CMD_FW;

   // BUF_FILL_WARN : DSI_CMD_FW
   logic[1:0]  DSI_CMD_FW;


   always_comb begin
       DSI_CMD_FW = buffer_interrupt_registers_BUF_FILL_WARN.DSI_CMD_FW_in;
   end

   assign buffer_interrupt_registers_BUF_FILL_WARN.DSI_CMD_FW = DSI_CMD_FW;

   // BUF_FILL_WARN : DSI_PDCM_FW
   logic[1:0]  DSI_PDCM_FW;


   always_comb begin
       DSI_PDCM_FW = buffer_interrupt_registers_BUF_FILL_WARN.DSI_PDCM_FW_in;
   end

   assign buffer_interrupt_registers_BUF_FILL_WARN.DSI_PDCM_FW = DSI_PDCM_FW;

   // BUF_FILL_WARN : DSI_CRM_FW
   logic[1:0]  DSI_CRM_FW;


   always_comb begin
       DSI_CRM_FW = buffer_interrupt_registers_BUF_FILL_WARN.DSI_CRM_FW_in;
   end

   assign buffer_interrupt_registers_BUF_FILL_WARN.DSI_CRM_FW = DSI_CRM_FW;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {9'd0, SPI_CMD_FW, DSI_CMD_FW, DSI_PDCM_FW, DSI_CRM_FW} : '0;

   assign buffer_interrupt_registers_BUF_FILL_WARN.value = {9'd0, SPI_CMD_FW, DSI_CMD_FW, DSI_PDCM_FW, DSI_CRM_FW};

endmodule : buffer_interrupt_registers_BUF_FILL_WARN

/*###   Registers   ######################################################*/
module buffer_interrupt_registers #(
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
   buffer_interrupt_registers_BUF_IRQ_STAT_if.master buffer_interrupt_registers_BUF_IRQ_STAT,
   buffer_interrupt_registers_BUF_IRQ_MASK_if.master buffer_interrupt_registers_BUF_IRQ_MASK,
   buffer_interrupt_registers_BUF_FILL_WARN_if.master buffer_interrupt_registers_BUF_FILL_WARN
);

   logic[15:0] data_out_BUF_IRQ_STAT, data_out_BUF_IRQ_MASK, data_out_BUF_FILL_WARN;

   buffer_interrupt_registers_BUF_IRQ_STAT #( .reg_addr (base_addr + 'h61), .addr_width(addr_width) ) i_buffer_interrupt_registers_BUF_IRQ_STAT ( .data_out (data_out_BUF_IRQ_STAT), .*);
   buffer_interrupt_registers_BUF_IRQ_MASK #( .reg_addr (base_addr + 'h62), .addr_width(addr_width) ) i_buffer_interrupt_registers_BUF_IRQ_MASK ( .data_out (data_out_BUF_IRQ_MASK), .*);
   buffer_interrupt_registers_BUF_FILL_WARN #( .reg_addr (base_addr + 'h63), .addr_width(addr_width) ) i_buffer_interrupt_registers_BUF_FILL_WARN ( .data_out (data_out_BUF_FILL_WARN), .*);

   // output data assignment
   assign data_out = data_out_BUF_IRQ_STAT | data_out_BUF_IRQ_MASK | data_out_BUF_FILL_WARN;

endmodule : buffer_interrupt_registers
