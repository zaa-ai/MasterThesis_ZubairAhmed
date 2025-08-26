/* ###   interfaces   ###################################################### */

// IRQ_STAT
interface Interrupt_Registers_IRQ_STAT_if;
  logic[15:0] value;
  logic HW_FAIL, HW_FAIL_in;
  logic RESERVED, RESERVED_in;
  logic ECC_FAIL, ECC_FAIL_in;
  logic SUPPLY, SUPPLY_in;
  logic[1:0] DSI, DSI_in;
  logic BUF, BUF_in;
  logic SPI, SPI_in;
  logic RESET;
  logic CLKREF, CLKREF_in;
  logic OTPFAIL, OTPFAIL_in;
  logic HW_FAIL_set, CLKREF_set, OTPFAIL_set;

  modport master (
    input HW_FAIL_in, RESERVED_in, ECC_FAIL_in, SUPPLY_in, DSI_in, BUF_in, SPI_in, CLKREF_in, OTPFAIL_in, HW_FAIL_set, CLKREF_set, OTPFAIL_set, 
    output value, HW_FAIL, RESERVED, ECC_FAIL, SUPPLY, DSI, BUF, SPI, RESET, CLKREF, OTPFAIL
  );

  modport slave (
    input value, HW_FAIL, RESERVED, ECC_FAIL, SUPPLY, DSI, BUF, SPI, RESET, CLKREF, OTPFAIL, 
    output HW_FAIL_in, RESERVED_in, ECC_FAIL_in, SUPPLY_in, DSI_in, BUF_in, SPI_in, CLKREF_in, OTPFAIL_in, HW_FAIL_set, CLKREF_set, OTPFAIL_set
  );

endinterface : Interrupt_Registers_IRQ_STAT_if

// IRQ_MASK
interface Interrupt_Registers_IRQ_MASK_if;
  logic[15:0] value;
  logic HW_FAIL;
  logic RESERVED;
  logic ECC_FAIL;
  logic SUPPLY;
  logic[1:0] DSI;
  logic BUF;
  logic SPI;
  logic RESET;
  logic CLKREF;
  logic OTPFAIL;

  modport master (
    output value, HW_FAIL, RESERVED, ECC_FAIL, SUPPLY, DSI, BUF, SPI, RESET, CLKREF, OTPFAIL
  );

  modport slave (
    input value, HW_FAIL, RESERVED, ECC_FAIL, SUPPLY, DSI, BUF, SPI, RESET, CLKREF, OTPFAIL
  );

endinterface : Interrupt_Registers_IRQ_MASK_if

// ECC_IRQ_STAT
interface Interrupt_Registers_ECC_IRQ_STAT_if;
  logic[15:0] value;
  logic RAM, RAM_in;
  logic SPI_DATA, SPI_DATA_in;
  logic SPI_CMD, SPI_CMD_in;
  logic SPI_CMD_BUF, SPI_CMD_BUF_in;
  logic[1:0] DSI_CMD, DSI_CMD_in;
  logic[1:0] DSI_TDMA, DSI_TDMA_in;
  logic[1:0] DSI_CMD_BUF, DSI_CMD_BUF_in;
  logic[1:0] DSI_PDCM_DATA_BUF, DSI_PDCM_DATA_BUF_in;
  logic[1:0] DSI_CRM_DATA_BUF, DSI_CRM_DATA_BUF_in;
  logic RAM_set, SPI_DATA_set, SPI_CMD_set, SPI_CMD_BUF_set, DSI_CMD_set, DSI_TDMA_set, DSI_CMD_BUF_set, DSI_PDCM_DATA_BUF_set, DSI_CRM_DATA_BUF_set;

  modport master (
    input RAM_in, SPI_DATA_in, SPI_CMD_in, SPI_CMD_BUF_in, DSI_CMD_in, DSI_TDMA_in, DSI_CMD_BUF_in, DSI_PDCM_DATA_BUF_in, DSI_CRM_DATA_BUF_in, RAM_set, SPI_DATA_set, SPI_CMD_set, SPI_CMD_BUF_set, DSI_CMD_set, DSI_TDMA_set, DSI_CMD_BUF_set, DSI_PDCM_DATA_BUF_set, DSI_CRM_DATA_BUF_set, 
    output value, RAM, SPI_DATA, SPI_CMD, SPI_CMD_BUF, DSI_CMD, DSI_TDMA, DSI_CMD_BUF, DSI_PDCM_DATA_BUF, DSI_CRM_DATA_BUF
  );

  modport slave (
    input value, RAM, SPI_DATA, SPI_CMD, SPI_CMD_BUF, DSI_CMD, DSI_TDMA, DSI_CMD_BUF, DSI_PDCM_DATA_BUF, DSI_CRM_DATA_BUF, 
    output RAM_in, SPI_DATA_in, SPI_CMD_in, SPI_CMD_BUF_in, DSI_CMD_in, DSI_TDMA_in, DSI_CMD_BUF_in, DSI_PDCM_DATA_BUF_in, DSI_CRM_DATA_BUF_in, RAM_set, SPI_DATA_set, SPI_CMD_set, SPI_CMD_BUF_set, DSI_CMD_set, DSI_TDMA_set, DSI_CMD_BUF_set, DSI_PDCM_DATA_BUF_set, DSI_CRM_DATA_BUF_set
  );

endinterface : Interrupt_Registers_ECC_IRQ_STAT_if

// ECC_IRQ_MASK
interface Interrupt_Registers_ECC_IRQ_MASK_if;
  logic[15:0] value;
  logic RAM;
  logic SPI_DATA;
  logic SPI_CMD;
  logic SPI_CMD_BUF;
  logic[1:0] DSI_CMD;
  logic[1:0] DSI_TDMA;
  logic[1:0] DSI_CMD_BUF;
  logic[1:0] DSI_PDCM_DATA_BUF;
  logic[1:0] DSI_CRM_DATA_BUF;

  modport master (
    output value, RAM, SPI_DATA, SPI_CMD, SPI_CMD_BUF, DSI_CMD, DSI_TDMA, DSI_CMD_BUF, DSI_PDCM_DATA_BUF, DSI_CRM_DATA_BUF
  );

  modport slave (
    input value, RAM, SPI_DATA, SPI_CMD, SPI_CMD_BUF, DSI_CMD, DSI_TDMA, DSI_CMD_BUF, DSI_PDCM_DATA_BUF, DSI_CRM_DATA_BUF
  );

endinterface : Interrupt_Registers_ECC_IRQ_MASK_if

// ECC_CORR_IRQ_STAT
interface Interrupt_Registers_ECC_CORR_IRQ_STAT_if;
  logic[15:0] value;
  logic RAM, RAM_in;
  logic SPI_DATA, SPI_DATA_in;
  logic SPI_CMD, SPI_CMD_in;
  logic SPI_CMD_BUF, SPI_CMD_BUF_in;
  logic[1:0] DSI_CMD, DSI_CMD_in;
  logic[1:0] DSI_TDMA, DSI_TDMA_in;
  logic[1:0] DSI_CMD_BUF, DSI_CMD_BUF_in;
  logic[1:0] DSI_PDCM_DATA_BUF, DSI_PDCM_DATA_BUF_in;
  logic[1:0] DSI_CRM_DATA_BUF, DSI_CRM_DATA_BUF_in;
  logic RAM_set, SPI_DATA_set, SPI_CMD_set, SPI_CMD_BUF_set, DSI_CMD_set, DSI_TDMA_set, DSI_CMD_BUF_set, DSI_PDCM_DATA_BUF_set, DSI_CRM_DATA_BUF_set;

  modport master (
    input RAM_in, SPI_DATA_in, SPI_CMD_in, SPI_CMD_BUF_in, DSI_CMD_in, DSI_TDMA_in, DSI_CMD_BUF_in, DSI_PDCM_DATA_BUF_in, DSI_CRM_DATA_BUF_in, RAM_set, SPI_DATA_set, SPI_CMD_set, SPI_CMD_BUF_set, DSI_CMD_set, DSI_TDMA_set, DSI_CMD_BUF_set, DSI_PDCM_DATA_BUF_set, DSI_CRM_DATA_BUF_set, 
    output value, RAM, SPI_DATA, SPI_CMD, SPI_CMD_BUF, DSI_CMD, DSI_TDMA, DSI_CMD_BUF, DSI_PDCM_DATA_BUF, DSI_CRM_DATA_BUF
  );

  modport slave (
    input value, RAM, SPI_DATA, SPI_CMD, SPI_CMD_BUF, DSI_CMD, DSI_TDMA, DSI_CMD_BUF, DSI_PDCM_DATA_BUF, DSI_CRM_DATA_BUF, 
    output RAM_in, SPI_DATA_in, SPI_CMD_in, SPI_CMD_BUF_in, DSI_CMD_in, DSI_TDMA_in, DSI_CMD_BUF_in, DSI_PDCM_DATA_BUF_in, DSI_CRM_DATA_BUF_in, RAM_set, SPI_DATA_set, SPI_CMD_set, SPI_CMD_BUF_set, DSI_CMD_set, DSI_TDMA_set, DSI_CMD_BUF_set, DSI_PDCM_DATA_BUF_set, DSI_CRM_DATA_BUF_set
  );

endinterface : Interrupt_Registers_ECC_CORR_IRQ_STAT_if

// ECC_CORR_IRQ_MASK
interface Interrupt_Registers_ECC_CORR_IRQ_MASK_if;
  logic[15:0] value;
  logic RAM;
  logic SPI_DATA;
  logic SPI_CMD;
  logic SPI_CMD_BUF;
  logic[1:0] DSI_CMD;
  logic[1:0] DSI_TDMA;
  logic[1:0] DSI_CMD_BUF;
  logic[1:0] DSI_PDCM_DATA_BUF;
  logic[1:0] DSI_CRM_DATA_BUF;

  modport master (
    output value, RAM, SPI_DATA, SPI_CMD, SPI_CMD_BUF, DSI_CMD, DSI_TDMA, DSI_CMD_BUF, DSI_PDCM_DATA_BUF, DSI_CRM_DATA_BUF
  );

  modport slave (
    input value, RAM, SPI_DATA, SPI_CMD, SPI_CMD_BUF, DSI_CMD, DSI_TDMA, DSI_CMD_BUF, DSI_PDCM_DATA_BUF, DSI_CRM_DATA_BUF
  );

endinterface : Interrupt_Registers_ECC_CORR_IRQ_MASK_if



/*###   IRQ_STAT   ######################################################*/
module Interrupt_Registers_IRQ_STAT #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   Interrupt_Registers_IRQ_STAT_if.master Interrupt_Registers_IRQ_STAT);

   // IRQ_STAT : HW_FAIL
   logic  HW_FAIL, HW_FAIL_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       HW_FAIL <= 1'b0;
     end
     else begin
       HW_FAIL <= HW_FAIL_nxt;
     end
   end

   always_comb begin
     HW_FAIL_nxt = HW_FAIL;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[12])) begin
       HW_FAIL_nxt = HW_FAIL & (~data_in[12]);
     end
     if (Interrupt_Registers_IRQ_STAT.HW_FAIL_set == 1'b1) begin
       HW_FAIL_nxt = Interrupt_Registers_IRQ_STAT.HW_FAIL_in;
     end
   end

   assign Interrupt_Registers_IRQ_STAT.HW_FAIL = HW_FAIL;

   `ifdef VCS

     property HW_FAIL_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (Interrupt_Registers_IRQ_STAT.HW_FAIL_set !== 1'bx);
     endproperty
      as_HW_FAIL_set_not_x : assert property (HW_FAIL_set_not_x) else $error("Interrupt_Registers_IRQ_STAT.HW_FAIL_set is x after reset");
     cov_HW_FAIL_set_not_x :  cover property (HW_FAIL_set_not_x);

   `endif

   // IRQ_STAT : RESERVED
   logic  RESERVED;


   always_comb begin
       RESERVED = Interrupt_Registers_IRQ_STAT.RESERVED_in;
   end

   assign Interrupt_Registers_IRQ_STAT.RESERVED = RESERVED;

   // IRQ_STAT : ECC_FAIL
   logic  ECC_FAIL;


   always_comb begin
       ECC_FAIL = Interrupt_Registers_IRQ_STAT.ECC_FAIL_in;
   end

   assign Interrupt_Registers_IRQ_STAT.ECC_FAIL = ECC_FAIL;

   // IRQ_STAT : SUPPLY
   logic  SUPPLY;


   always_comb begin
       SUPPLY = Interrupt_Registers_IRQ_STAT.SUPPLY_in;
   end

   assign Interrupt_Registers_IRQ_STAT.SUPPLY = SUPPLY;

   // IRQ_STAT : DSI
   logic[1:0]  DSI;


   always_comb begin
       DSI = Interrupt_Registers_IRQ_STAT.DSI_in;
   end

   assign Interrupt_Registers_IRQ_STAT.DSI = DSI;

   // IRQ_STAT : BUF
   logic  BUF;


   always_comb begin
       BUF = Interrupt_Registers_IRQ_STAT.BUF_in;
   end

   assign Interrupt_Registers_IRQ_STAT.BUF = BUF;

   // IRQ_STAT : SPI
   logic  SPI;


   always_comb begin
       SPI = Interrupt_Registers_IRQ_STAT.SPI_in;
   end

   assign Interrupt_Registers_IRQ_STAT.SPI = SPI;

   // IRQ_STAT : RESET
   logic  RESET, RESET_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       RESET <= 1'b1;
     end
     else begin
       RESET <= RESET_nxt;
     end
   end

   always_comb begin
     RESET_nxt = RESET;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[2])) begin
       RESET_nxt = RESET & (~data_in[2]);
     end
   end

   assign Interrupt_Registers_IRQ_STAT.RESET = RESET;

   // IRQ_STAT : CLKREF
   logic  CLKREF, CLKREF_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       CLKREF <= 1'b0;
     end
     else begin
       CLKREF <= CLKREF_nxt;
     end
   end

   always_comb begin
     CLKREF_nxt = CLKREF;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[1])) begin
       CLKREF_nxt = CLKREF & (~data_in[1]);
     end
     if (Interrupt_Registers_IRQ_STAT.CLKREF_set == 1'b1) begin
       CLKREF_nxt = Interrupt_Registers_IRQ_STAT.CLKREF_in;
     end
   end

   assign Interrupt_Registers_IRQ_STAT.CLKREF = CLKREF;

   `ifdef VCS

     property CLKREF_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (Interrupt_Registers_IRQ_STAT.CLKREF_set !== 1'bx);
     endproperty
      as_CLKREF_set_not_x : assert property (CLKREF_set_not_x) else $error("Interrupt_Registers_IRQ_STAT.CLKREF_set is x after reset");
     cov_CLKREF_set_not_x :  cover property (CLKREF_set_not_x);

   `endif

   // IRQ_STAT : OTPFAIL
   logic  OTPFAIL, OTPFAIL_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       OTPFAIL <= 1'b0;
     end
     else begin
       OTPFAIL <= OTPFAIL_nxt;
     end
   end

   always_comb begin
     OTPFAIL_nxt = OTPFAIL;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[0])) begin
       OTPFAIL_nxt = OTPFAIL & (~data_in[0]);
     end
     if (Interrupt_Registers_IRQ_STAT.OTPFAIL_set == 1'b1) begin
       OTPFAIL_nxt = Interrupt_Registers_IRQ_STAT.OTPFAIL_in;
     end
   end

   assign Interrupt_Registers_IRQ_STAT.OTPFAIL = OTPFAIL;

   `ifdef VCS

     property OTPFAIL_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (Interrupt_Registers_IRQ_STAT.OTPFAIL_set !== 1'bx);
     endproperty
      as_OTPFAIL_set_not_x : assert property (OTPFAIL_set_not_x) else $error("Interrupt_Registers_IRQ_STAT.OTPFAIL_set is x after reset");
     cov_OTPFAIL_set_not_x :  cover property (OTPFAIL_set_not_x);

   `endif

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {3'd0, HW_FAIL, RESERVED, ECC_FAIL, SUPPLY, 2'd0, DSI, BUF, SPI, RESET, CLKREF, OTPFAIL} : '0;

   assign Interrupt_Registers_IRQ_STAT.value = {3'd0, HW_FAIL, RESERVED, ECC_FAIL, SUPPLY, 2'd0, DSI, BUF, SPI, RESET, CLKREF, OTPFAIL};

endmodule : Interrupt_Registers_IRQ_STAT

/*###   IRQ_MASK   ######################################################*/
module Interrupt_Registers_IRQ_MASK #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   Interrupt_Registers_IRQ_MASK_if.master Interrupt_Registers_IRQ_MASK);

   // IRQ_MASK : HW_FAIL
   logic  HW_FAIL, HW_FAIL_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       HW_FAIL <= 1'b1;
     end
     else begin
       HW_FAIL <= HW_FAIL_nxt;
     end
   end

   always_comb begin
     HW_FAIL_nxt = HW_FAIL;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       HW_FAIL_nxt = data_in[12:12]; 
     end
   end

   assign Interrupt_Registers_IRQ_MASK.HW_FAIL = HW_FAIL;

   // IRQ_MASK : RESERVED
   logic  RESERVED, RESERVED_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       RESERVED <= 1'b0;
     end
     else begin
       RESERVED <= RESERVED_nxt;
     end
   end

   always_comb begin
     RESERVED_nxt = RESERVED;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       RESERVED_nxt = data_in[11:11]; 
     end
   end

   assign Interrupt_Registers_IRQ_MASK.RESERVED = RESERVED;

   // IRQ_MASK : ECC_FAIL
   logic  ECC_FAIL, ECC_FAIL_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       ECC_FAIL <= 1'b1;
     end
     else begin
       ECC_FAIL <= ECC_FAIL_nxt;
     end
   end

   always_comb begin
     ECC_FAIL_nxt = ECC_FAIL;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       ECC_FAIL_nxt = data_in[10:10]; 
     end
   end

   assign Interrupt_Registers_IRQ_MASK.ECC_FAIL = ECC_FAIL;

   // IRQ_MASK : SUPPLY
   logic  SUPPLY, SUPPLY_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       SUPPLY <= 1'b1;
     end
     else begin
       SUPPLY <= SUPPLY_nxt;
     end
   end

   always_comb begin
     SUPPLY_nxt = SUPPLY;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       SUPPLY_nxt = data_in[9:9]; 
     end
   end

   assign Interrupt_Registers_IRQ_MASK.SUPPLY = SUPPLY;

   // IRQ_MASK : DSI
   logic[1:0]  DSI, DSI_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DSI <= 2'b11;
     end
     else begin
       DSI <= DSI_nxt;
     end
   end

   always_comb begin
     DSI_nxt = DSI;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       DSI_nxt = data_in[6:5]; 
     end
   end

   assign Interrupt_Registers_IRQ_MASK.DSI = DSI;

   // IRQ_MASK : BUF
   logic  BUF, BUF_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       BUF <= 1'b1;
     end
     else begin
       BUF <= BUF_nxt;
     end
   end

   always_comb begin
     BUF_nxt = BUF;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       BUF_nxt = data_in[4:4]; 
     end
   end

   assign Interrupt_Registers_IRQ_MASK.BUF = BUF;

   // IRQ_MASK : SPI
   logic  SPI, SPI_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       SPI <= 1'b1;
     end
     else begin
       SPI <= SPI_nxt;
     end
   end

   always_comb begin
     SPI_nxt = SPI;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       SPI_nxt = data_in[3:3]; 
     end
   end

   assign Interrupt_Registers_IRQ_MASK.SPI = SPI;

   // IRQ_MASK : RESET
   logic  RESET, RESET_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       RESET <= 1'b1;
     end
     else begin
       RESET <= RESET_nxt;
     end
   end

   always_comb begin
     RESET_nxt = RESET;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       RESET_nxt = data_in[2:2]; 
     end
   end

   assign Interrupt_Registers_IRQ_MASK.RESET = RESET;

   // IRQ_MASK : CLKREF
   logic  CLKREF, CLKREF_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       CLKREF <= 1'b1;
     end
     else begin
       CLKREF <= CLKREF_nxt;
     end
   end

   always_comb begin
     CLKREF_nxt = CLKREF;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       CLKREF_nxt = data_in[1:1]; 
     end
   end

   assign Interrupt_Registers_IRQ_MASK.CLKREF = CLKREF;

   // IRQ_MASK : OTPFAIL
   logic  OTPFAIL, OTPFAIL_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       OTPFAIL <= 1'b1;
     end
     else begin
       OTPFAIL <= OTPFAIL_nxt;
     end
   end

   always_comb begin
     OTPFAIL_nxt = OTPFAIL;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       OTPFAIL_nxt = data_in[0:0]; 
     end
   end

   assign Interrupt_Registers_IRQ_MASK.OTPFAIL = OTPFAIL;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {3'd0, HW_FAIL, RESERVED, ECC_FAIL, SUPPLY, 2'd0, DSI, BUF, SPI, RESET, CLKREF, OTPFAIL} : '0;

   assign Interrupt_Registers_IRQ_MASK.value = {3'd0, HW_FAIL, RESERVED, ECC_FAIL, SUPPLY, 2'd0, DSI, BUF, SPI, RESET, CLKREF, OTPFAIL};

endmodule : Interrupt_Registers_IRQ_MASK

/*###   ECC_IRQ_STAT   ######################################################*/
module Interrupt_Registers_ECC_IRQ_STAT #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   Interrupt_Registers_ECC_IRQ_STAT_if.master Interrupt_Registers_ECC_IRQ_STAT);

   // ECC_IRQ_STAT : RAM
   logic  RAM, RAM_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       RAM <= 1'b0;
     end
     else begin
       RAM <= RAM_nxt;
     end
   end

   always_comb begin
     RAM_nxt = RAM;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[15])) begin
       RAM_nxt = RAM & (~data_in[15]);
     end
     if (Interrupt_Registers_ECC_IRQ_STAT.RAM_set == 1'b1) begin
       RAM_nxt = Interrupt_Registers_ECC_IRQ_STAT.RAM_in;
     end
   end

   assign Interrupt_Registers_ECC_IRQ_STAT.RAM = RAM;

   `ifdef VCS

     property RAM_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (Interrupt_Registers_ECC_IRQ_STAT.RAM_set !== 1'bx);
     endproperty
      as_RAM_set_not_x : assert property (RAM_set_not_x) else $error("Interrupt_Registers_ECC_IRQ_STAT.RAM_set is x after reset");
     cov_RAM_set_not_x :  cover property (RAM_set_not_x);

   `endif

   // ECC_IRQ_STAT : SPI_DATA
   logic  SPI_DATA, SPI_DATA_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       SPI_DATA <= 1'b0;
     end
     else begin
       SPI_DATA <= SPI_DATA_nxt;
     end
   end

   always_comb begin
     SPI_DATA_nxt = SPI_DATA;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[14])) begin
       SPI_DATA_nxt = SPI_DATA & (~data_in[14]);
     end
     if (Interrupt_Registers_ECC_IRQ_STAT.SPI_DATA_set == 1'b1) begin
       SPI_DATA_nxt = Interrupt_Registers_ECC_IRQ_STAT.SPI_DATA_in;
     end
   end

   assign Interrupt_Registers_ECC_IRQ_STAT.SPI_DATA = SPI_DATA;

   `ifdef VCS

     property SPI_DATA_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (Interrupt_Registers_ECC_IRQ_STAT.SPI_DATA_set !== 1'bx);
     endproperty
      as_SPI_DATA_set_not_x : assert property (SPI_DATA_set_not_x) else $error("Interrupt_Registers_ECC_IRQ_STAT.SPI_DATA_set is x after reset");
     cov_SPI_DATA_set_not_x :  cover property (SPI_DATA_set_not_x);

   `endif

   // ECC_IRQ_STAT : SPI_CMD
   logic  SPI_CMD, SPI_CMD_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       SPI_CMD <= 1'b0;
     end
     else begin
       SPI_CMD <= SPI_CMD_nxt;
     end
   end

   always_comb begin
     SPI_CMD_nxt = SPI_CMD;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[13])) begin
       SPI_CMD_nxt = SPI_CMD & (~data_in[13]);
     end
     if (Interrupt_Registers_ECC_IRQ_STAT.SPI_CMD_set == 1'b1) begin
       SPI_CMD_nxt = Interrupt_Registers_ECC_IRQ_STAT.SPI_CMD_in;
     end
   end

   assign Interrupt_Registers_ECC_IRQ_STAT.SPI_CMD = SPI_CMD;

   `ifdef VCS

     property SPI_CMD_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (Interrupt_Registers_ECC_IRQ_STAT.SPI_CMD_set !== 1'bx);
     endproperty
      as_SPI_CMD_set_not_x : assert property (SPI_CMD_set_not_x) else $error("Interrupt_Registers_ECC_IRQ_STAT.SPI_CMD_set is x after reset");
     cov_SPI_CMD_set_not_x :  cover property (SPI_CMD_set_not_x);

   `endif

   // ECC_IRQ_STAT : SPI_CMD_BUF
   logic  SPI_CMD_BUF, SPI_CMD_BUF_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       SPI_CMD_BUF <= 1'b0;
     end
     else begin
       SPI_CMD_BUF <= SPI_CMD_BUF_nxt;
     end
   end

   always_comb begin
     SPI_CMD_BUF_nxt = SPI_CMD_BUF;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[12])) begin
       SPI_CMD_BUF_nxt = SPI_CMD_BUF & (~data_in[12]);
     end
     if (Interrupt_Registers_ECC_IRQ_STAT.SPI_CMD_BUF_set == 1'b1) begin
       SPI_CMD_BUF_nxt = Interrupt_Registers_ECC_IRQ_STAT.SPI_CMD_BUF_in;
     end
   end

   assign Interrupt_Registers_ECC_IRQ_STAT.SPI_CMD_BUF = SPI_CMD_BUF;

   `ifdef VCS

     property SPI_CMD_BUF_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (Interrupt_Registers_ECC_IRQ_STAT.SPI_CMD_BUF_set !== 1'bx);
     endproperty
      as_SPI_CMD_BUF_set_not_x : assert property (SPI_CMD_BUF_set_not_x) else $error("Interrupt_Registers_ECC_IRQ_STAT.SPI_CMD_BUF_set is x after reset");
     cov_SPI_CMD_BUF_set_not_x :  cover property (SPI_CMD_BUF_set_not_x);

   `endif

   // ECC_IRQ_STAT : DSI_CMD
   logic[1:0]  DSI_CMD, DSI_CMD_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DSI_CMD <= 2'b0;
     end
     else begin
       DSI_CMD <= DSI_CMD_nxt;
     end
   end

   always_comb begin
     DSI_CMD_nxt = DSI_CMD;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[9:8])) begin
       DSI_CMD_nxt = DSI_CMD & (~data_in[9:8]);
     end
     if (Interrupt_Registers_ECC_IRQ_STAT.DSI_CMD_set == 1'b1) begin
       DSI_CMD_nxt = Interrupt_Registers_ECC_IRQ_STAT.DSI_CMD_in;
     end
   end

   assign Interrupt_Registers_ECC_IRQ_STAT.DSI_CMD = DSI_CMD;

   `ifdef VCS

     property DSI_CMD_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (Interrupt_Registers_ECC_IRQ_STAT.DSI_CMD_set !== 1'bx);
     endproperty
      as_DSI_CMD_set_not_x : assert property (DSI_CMD_set_not_x) else $error("Interrupt_Registers_ECC_IRQ_STAT.DSI_CMD_set is x after reset");
     cov_DSI_CMD_set_not_x :  cover property (DSI_CMD_set_not_x);

   `endif

   // ECC_IRQ_STAT : DSI_TDMA
   logic[1:0]  DSI_TDMA, DSI_TDMA_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DSI_TDMA <= 2'b0;
     end
     else begin
       DSI_TDMA <= DSI_TDMA_nxt;
     end
   end

   always_comb begin
     DSI_TDMA_nxt = DSI_TDMA;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[7:6])) begin
       DSI_TDMA_nxt = DSI_TDMA & (~data_in[7:6]);
     end
     if (Interrupt_Registers_ECC_IRQ_STAT.DSI_TDMA_set == 1'b1) begin
       DSI_TDMA_nxt = Interrupt_Registers_ECC_IRQ_STAT.DSI_TDMA_in;
     end
   end

   assign Interrupt_Registers_ECC_IRQ_STAT.DSI_TDMA = DSI_TDMA;

   `ifdef VCS

     property DSI_TDMA_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (Interrupt_Registers_ECC_IRQ_STAT.DSI_TDMA_set !== 1'bx);
     endproperty
      as_DSI_TDMA_set_not_x : assert property (DSI_TDMA_set_not_x) else $error("Interrupt_Registers_ECC_IRQ_STAT.DSI_TDMA_set is x after reset");
     cov_DSI_TDMA_set_not_x :  cover property (DSI_TDMA_set_not_x);

   `endif

   // ECC_IRQ_STAT : DSI_CMD_BUF
   logic[1:0]  DSI_CMD_BUF, DSI_CMD_BUF_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DSI_CMD_BUF <= 2'b0;
     end
     else begin
       DSI_CMD_BUF <= DSI_CMD_BUF_nxt;
     end
   end

   always_comb begin
     DSI_CMD_BUF_nxt = DSI_CMD_BUF;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[5:4])) begin
       DSI_CMD_BUF_nxt = DSI_CMD_BUF & (~data_in[5:4]);
     end
     if (Interrupt_Registers_ECC_IRQ_STAT.DSI_CMD_BUF_set == 1'b1) begin
       DSI_CMD_BUF_nxt = Interrupt_Registers_ECC_IRQ_STAT.DSI_CMD_BUF_in;
     end
   end

   assign Interrupt_Registers_ECC_IRQ_STAT.DSI_CMD_BUF = DSI_CMD_BUF;

   `ifdef VCS

     property DSI_CMD_BUF_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (Interrupt_Registers_ECC_IRQ_STAT.DSI_CMD_BUF_set !== 1'bx);
     endproperty
      as_DSI_CMD_BUF_set_not_x : assert property (DSI_CMD_BUF_set_not_x) else $error("Interrupt_Registers_ECC_IRQ_STAT.DSI_CMD_BUF_set is x after reset");
     cov_DSI_CMD_BUF_set_not_x :  cover property (DSI_CMD_BUF_set_not_x);

   `endif

   // ECC_IRQ_STAT : DSI_PDCM_DATA_BUF
   logic[1:0]  DSI_PDCM_DATA_BUF, DSI_PDCM_DATA_BUF_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DSI_PDCM_DATA_BUF <= 2'b0;
     end
     else begin
       DSI_PDCM_DATA_BUF <= DSI_PDCM_DATA_BUF_nxt;
     end
   end

   always_comb begin
     DSI_PDCM_DATA_BUF_nxt = DSI_PDCM_DATA_BUF;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[3:2])) begin
       DSI_PDCM_DATA_BUF_nxt = DSI_PDCM_DATA_BUF & (~data_in[3:2]);
     end
     if (Interrupt_Registers_ECC_IRQ_STAT.DSI_PDCM_DATA_BUF_set == 1'b1) begin
       DSI_PDCM_DATA_BUF_nxt = Interrupt_Registers_ECC_IRQ_STAT.DSI_PDCM_DATA_BUF_in;
     end
   end

   assign Interrupt_Registers_ECC_IRQ_STAT.DSI_PDCM_DATA_BUF = DSI_PDCM_DATA_BUF;

   `ifdef VCS

     property DSI_PDCM_DATA_BUF_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (Interrupt_Registers_ECC_IRQ_STAT.DSI_PDCM_DATA_BUF_set !== 1'bx);
     endproperty
      as_DSI_PDCM_DATA_BUF_set_not_x : assert property (DSI_PDCM_DATA_BUF_set_not_x) else $error("Interrupt_Registers_ECC_IRQ_STAT.DSI_PDCM_DATA_BUF_set is x after reset");
     cov_DSI_PDCM_DATA_BUF_set_not_x :  cover property (DSI_PDCM_DATA_BUF_set_not_x);

   `endif

   // ECC_IRQ_STAT : DSI_CRM_DATA_BUF
   logic[1:0]  DSI_CRM_DATA_BUF, DSI_CRM_DATA_BUF_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DSI_CRM_DATA_BUF <= 2'b0;
     end
     else begin
       DSI_CRM_DATA_BUF <= DSI_CRM_DATA_BUF_nxt;
     end
   end

   always_comb begin
     DSI_CRM_DATA_BUF_nxt = DSI_CRM_DATA_BUF;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[1:0])) begin
       DSI_CRM_DATA_BUF_nxt = DSI_CRM_DATA_BUF & (~data_in[1:0]);
     end
     if (Interrupt_Registers_ECC_IRQ_STAT.DSI_CRM_DATA_BUF_set == 1'b1) begin
       DSI_CRM_DATA_BUF_nxt = Interrupt_Registers_ECC_IRQ_STAT.DSI_CRM_DATA_BUF_in;
     end
   end

   assign Interrupt_Registers_ECC_IRQ_STAT.DSI_CRM_DATA_BUF = DSI_CRM_DATA_BUF;

   `ifdef VCS

     property DSI_CRM_DATA_BUF_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (Interrupt_Registers_ECC_IRQ_STAT.DSI_CRM_DATA_BUF_set !== 1'bx);
     endproperty
      as_DSI_CRM_DATA_BUF_set_not_x : assert property (DSI_CRM_DATA_BUF_set_not_x) else $error("Interrupt_Registers_ECC_IRQ_STAT.DSI_CRM_DATA_BUF_set is x after reset");
     cov_DSI_CRM_DATA_BUF_set_not_x :  cover property (DSI_CRM_DATA_BUF_set_not_x);

   `endif

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {RAM, SPI_DATA, SPI_CMD, SPI_CMD_BUF, 2'd0, DSI_CMD, DSI_TDMA, DSI_CMD_BUF, DSI_PDCM_DATA_BUF, DSI_CRM_DATA_BUF} : '0;

   assign Interrupt_Registers_ECC_IRQ_STAT.value = {RAM, SPI_DATA, SPI_CMD, SPI_CMD_BUF, 2'd0, DSI_CMD, DSI_TDMA, DSI_CMD_BUF, DSI_PDCM_DATA_BUF, DSI_CRM_DATA_BUF};

endmodule : Interrupt_Registers_ECC_IRQ_STAT

/*###   ECC_IRQ_MASK   ######################################################*/
module Interrupt_Registers_ECC_IRQ_MASK #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   Interrupt_Registers_ECC_IRQ_MASK_if.master Interrupt_Registers_ECC_IRQ_MASK);

   // ECC_IRQ_MASK : RAM
   logic  RAM, RAM_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       RAM <= 1'b1;
     end
     else begin
       RAM <= RAM_nxt;
     end
   end

   always_comb begin
     RAM_nxt = RAM;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       RAM_nxt = data_in[15:15]; 
     end
   end

   assign Interrupt_Registers_ECC_IRQ_MASK.RAM = RAM;

   // ECC_IRQ_MASK : SPI_DATA
   logic  SPI_DATA, SPI_DATA_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       SPI_DATA <= 1'b1;
     end
     else begin
       SPI_DATA <= SPI_DATA_nxt;
     end
   end

   always_comb begin
     SPI_DATA_nxt = SPI_DATA;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       SPI_DATA_nxt = data_in[14:14]; 
     end
   end

   assign Interrupt_Registers_ECC_IRQ_MASK.SPI_DATA = SPI_DATA;

   // ECC_IRQ_MASK : SPI_CMD
   logic  SPI_CMD, SPI_CMD_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       SPI_CMD <= 1'b1;
     end
     else begin
       SPI_CMD <= SPI_CMD_nxt;
     end
   end

   always_comb begin
     SPI_CMD_nxt = SPI_CMD;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       SPI_CMD_nxt = data_in[13:13]; 
     end
   end

   assign Interrupt_Registers_ECC_IRQ_MASK.SPI_CMD = SPI_CMD;

   // ECC_IRQ_MASK : SPI_CMD_BUF
   logic  SPI_CMD_BUF, SPI_CMD_BUF_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       SPI_CMD_BUF <= 1'b1;
     end
     else begin
       SPI_CMD_BUF <= SPI_CMD_BUF_nxt;
     end
   end

   always_comb begin
     SPI_CMD_BUF_nxt = SPI_CMD_BUF;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       SPI_CMD_BUF_nxt = data_in[12:12]; 
     end
   end

   assign Interrupt_Registers_ECC_IRQ_MASK.SPI_CMD_BUF = SPI_CMD_BUF;

   // ECC_IRQ_MASK : DSI_CMD
   logic[1:0]  DSI_CMD, DSI_CMD_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DSI_CMD <= 2'b11;
     end
     else begin
       DSI_CMD <= DSI_CMD_nxt;
     end
   end

   always_comb begin
     DSI_CMD_nxt = DSI_CMD;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       DSI_CMD_nxt = data_in[9:8]; 
     end
   end

   assign Interrupt_Registers_ECC_IRQ_MASK.DSI_CMD = DSI_CMD;

   // ECC_IRQ_MASK : DSI_TDMA
   logic[1:0]  DSI_TDMA, DSI_TDMA_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DSI_TDMA <= 2'b11;
     end
     else begin
       DSI_TDMA <= DSI_TDMA_nxt;
     end
   end

   always_comb begin
     DSI_TDMA_nxt = DSI_TDMA;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       DSI_TDMA_nxt = data_in[7:6]; 
     end
   end

   assign Interrupt_Registers_ECC_IRQ_MASK.DSI_TDMA = DSI_TDMA;

   // ECC_IRQ_MASK : DSI_CMD_BUF
   logic[1:0]  DSI_CMD_BUF, DSI_CMD_BUF_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DSI_CMD_BUF <= 2'b11;
     end
     else begin
       DSI_CMD_BUF <= DSI_CMD_BUF_nxt;
     end
   end

   always_comb begin
     DSI_CMD_BUF_nxt = DSI_CMD_BUF;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       DSI_CMD_BUF_nxt = data_in[5:4]; 
     end
   end

   assign Interrupt_Registers_ECC_IRQ_MASK.DSI_CMD_BUF = DSI_CMD_BUF;

   // ECC_IRQ_MASK : DSI_PDCM_DATA_BUF
   logic[1:0]  DSI_PDCM_DATA_BUF, DSI_PDCM_DATA_BUF_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DSI_PDCM_DATA_BUF <= 2'b11;
     end
     else begin
       DSI_PDCM_DATA_BUF <= DSI_PDCM_DATA_BUF_nxt;
     end
   end

   always_comb begin
     DSI_PDCM_DATA_BUF_nxt = DSI_PDCM_DATA_BUF;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       DSI_PDCM_DATA_BUF_nxt = data_in[3:2]; 
     end
   end

   assign Interrupt_Registers_ECC_IRQ_MASK.DSI_PDCM_DATA_BUF = DSI_PDCM_DATA_BUF;

   // ECC_IRQ_MASK : DSI_CRM_DATA_BUF
   logic[1:0]  DSI_CRM_DATA_BUF, DSI_CRM_DATA_BUF_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DSI_CRM_DATA_BUF <= 2'b11;
     end
     else begin
       DSI_CRM_DATA_BUF <= DSI_CRM_DATA_BUF_nxt;
     end
   end

   always_comb begin
     DSI_CRM_DATA_BUF_nxt = DSI_CRM_DATA_BUF;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       DSI_CRM_DATA_BUF_nxt = data_in[1:0]; 
     end
   end

   assign Interrupt_Registers_ECC_IRQ_MASK.DSI_CRM_DATA_BUF = DSI_CRM_DATA_BUF;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {RAM, SPI_DATA, SPI_CMD, SPI_CMD_BUF, 2'd0, DSI_CMD, DSI_TDMA, DSI_CMD_BUF, DSI_PDCM_DATA_BUF, DSI_CRM_DATA_BUF} : '0;

   assign Interrupt_Registers_ECC_IRQ_MASK.value = {RAM, SPI_DATA, SPI_CMD, SPI_CMD_BUF, 2'd0, DSI_CMD, DSI_TDMA, DSI_CMD_BUF, DSI_PDCM_DATA_BUF, DSI_CRM_DATA_BUF};

endmodule : Interrupt_Registers_ECC_IRQ_MASK

/*###   ECC_CORR_IRQ_STAT   ######################################################*/
module Interrupt_Registers_ECC_CORR_IRQ_STAT #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   Interrupt_Registers_ECC_CORR_IRQ_STAT_if.master Interrupt_Registers_ECC_CORR_IRQ_STAT);

   // ECC_CORR_IRQ_STAT : RAM
   logic  RAM, RAM_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       RAM <= 1'b0;
     end
     else begin
       RAM <= RAM_nxt;
     end
   end

   always_comb begin
     RAM_nxt = RAM;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[15])) begin
       RAM_nxt = RAM & (~data_in[15]);
     end
     if (Interrupt_Registers_ECC_CORR_IRQ_STAT.RAM_set == 1'b1) begin
       RAM_nxt = Interrupt_Registers_ECC_CORR_IRQ_STAT.RAM_in;
     end
   end

   assign Interrupt_Registers_ECC_CORR_IRQ_STAT.RAM = RAM;

   `ifdef VCS

     property RAM_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (Interrupt_Registers_ECC_CORR_IRQ_STAT.RAM_set !== 1'bx);
     endproperty
      as_RAM_set_not_x : assert property (RAM_set_not_x) else $error("Interrupt_Registers_ECC_CORR_IRQ_STAT.RAM_set is x after reset");
     cov_RAM_set_not_x :  cover property (RAM_set_not_x);

   `endif

   // ECC_CORR_IRQ_STAT : SPI_DATA
   logic  SPI_DATA, SPI_DATA_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       SPI_DATA <= 1'b0;
     end
     else begin
       SPI_DATA <= SPI_DATA_nxt;
     end
   end

   always_comb begin
     SPI_DATA_nxt = SPI_DATA;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[14])) begin
       SPI_DATA_nxt = SPI_DATA & (~data_in[14]);
     end
     if (Interrupt_Registers_ECC_CORR_IRQ_STAT.SPI_DATA_set == 1'b1) begin
       SPI_DATA_nxt = Interrupt_Registers_ECC_CORR_IRQ_STAT.SPI_DATA_in;
     end
   end

   assign Interrupt_Registers_ECC_CORR_IRQ_STAT.SPI_DATA = SPI_DATA;

   `ifdef VCS

     property SPI_DATA_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (Interrupt_Registers_ECC_CORR_IRQ_STAT.SPI_DATA_set !== 1'bx);
     endproperty
      as_SPI_DATA_set_not_x : assert property (SPI_DATA_set_not_x) else $error("Interrupt_Registers_ECC_CORR_IRQ_STAT.SPI_DATA_set is x after reset");
     cov_SPI_DATA_set_not_x :  cover property (SPI_DATA_set_not_x);

   `endif

   // ECC_CORR_IRQ_STAT : SPI_CMD
   logic  SPI_CMD, SPI_CMD_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       SPI_CMD <= 1'b0;
     end
     else begin
       SPI_CMD <= SPI_CMD_nxt;
     end
   end

   always_comb begin
     SPI_CMD_nxt = SPI_CMD;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[13])) begin
       SPI_CMD_nxt = SPI_CMD & (~data_in[13]);
     end
     if (Interrupt_Registers_ECC_CORR_IRQ_STAT.SPI_CMD_set == 1'b1) begin
       SPI_CMD_nxt = Interrupt_Registers_ECC_CORR_IRQ_STAT.SPI_CMD_in;
     end
   end

   assign Interrupt_Registers_ECC_CORR_IRQ_STAT.SPI_CMD = SPI_CMD;

   `ifdef VCS

     property SPI_CMD_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (Interrupt_Registers_ECC_CORR_IRQ_STAT.SPI_CMD_set !== 1'bx);
     endproperty
      as_SPI_CMD_set_not_x : assert property (SPI_CMD_set_not_x) else $error("Interrupt_Registers_ECC_CORR_IRQ_STAT.SPI_CMD_set is x after reset");
     cov_SPI_CMD_set_not_x :  cover property (SPI_CMD_set_not_x);

   `endif

   // ECC_CORR_IRQ_STAT : SPI_CMD_BUF
   logic  SPI_CMD_BUF, SPI_CMD_BUF_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       SPI_CMD_BUF <= 1'b0;
     end
     else begin
       SPI_CMD_BUF <= SPI_CMD_BUF_nxt;
     end
   end

   always_comb begin
     SPI_CMD_BUF_nxt = SPI_CMD_BUF;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[12])) begin
       SPI_CMD_BUF_nxt = SPI_CMD_BUF & (~data_in[12]);
     end
     if (Interrupt_Registers_ECC_CORR_IRQ_STAT.SPI_CMD_BUF_set == 1'b1) begin
       SPI_CMD_BUF_nxt = Interrupt_Registers_ECC_CORR_IRQ_STAT.SPI_CMD_BUF_in;
     end
   end

   assign Interrupt_Registers_ECC_CORR_IRQ_STAT.SPI_CMD_BUF = SPI_CMD_BUF;

   `ifdef VCS

     property SPI_CMD_BUF_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (Interrupt_Registers_ECC_CORR_IRQ_STAT.SPI_CMD_BUF_set !== 1'bx);
     endproperty
      as_SPI_CMD_BUF_set_not_x : assert property (SPI_CMD_BUF_set_not_x) else $error("Interrupt_Registers_ECC_CORR_IRQ_STAT.SPI_CMD_BUF_set is x after reset");
     cov_SPI_CMD_BUF_set_not_x :  cover property (SPI_CMD_BUF_set_not_x);

   `endif

   // ECC_CORR_IRQ_STAT : DSI_CMD
   logic[1:0]  DSI_CMD, DSI_CMD_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DSI_CMD <= 2'b0;
     end
     else begin
       DSI_CMD <= DSI_CMD_nxt;
     end
   end

   always_comb begin
     DSI_CMD_nxt = DSI_CMD;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[9:8])) begin
       DSI_CMD_nxt = DSI_CMD & (~data_in[9:8]);
     end
     if (Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_CMD_set == 1'b1) begin
       DSI_CMD_nxt = Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_CMD_in;
     end
   end

   assign Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_CMD = DSI_CMD;

   `ifdef VCS

     property DSI_CMD_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_CMD_set !== 1'bx);
     endproperty
      as_DSI_CMD_set_not_x : assert property (DSI_CMD_set_not_x) else $error("Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_CMD_set is x after reset");
     cov_DSI_CMD_set_not_x :  cover property (DSI_CMD_set_not_x);

   `endif

   // ECC_CORR_IRQ_STAT : DSI_TDMA
   logic[1:0]  DSI_TDMA, DSI_TDMA_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DSI_TDMA <= 2'b0;
     end
     else begin
       DSI_TDMA <= DSI_TDMA_nxt;
     end
   end

   always_comb begin
     DSI_TDMA_nxt = DSI_TDMA;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[7:6])) begin
       DSI_TDMA_nxt = DSI_TDMA & (~data_in[7:6]);
     end
     if (Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_TDMA_set == 1'b1) begin
       DSI_TDMA_nxt = Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_TDMA_in;
     end
   end

   assign Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_TDMA = DSI_TDMA;

   `ifdef VCS

     property DSI_TDMA_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_TDMA_set !== 1'bx);
     endproperty
      as_DSI_TDMA_set_not_x : assert property (DSI_TDMA_set_not_x) else $error("Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_TDMA_set is x after reset");
     cov_DSI_TDMA_set_not_x :  cover property (DSI_TDMA_set_not_x);

   `endif

   // ECC_CORR_IRQ_STAT : DSI_CMD_BUF
   logic[1:0]  DSI_CMD_BUF, DSI_CMD_BUF_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DSI_CMD_BUF <= 2'b0;
     end
     else begin
       DSI_CMD_BUF <= DSI_CMD_BUF_nxt;
     end
   end

   always_comb begin
     DSI_CMD_BUF_nxt = DSI_CMD_BUF;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[5:4])) begin
       DSI_CMD_BUF_nxt = DSI_CMD_BUF & (~data_in[5:4]);
     end
     if (Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_CMD_BUF_set == 1'b1) begin
       DSI_CMD_BUF_nxt = Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_CMD_BUF_in;
     end
   end

   assign Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_CMD_BUF = DSI_CMD_BUF;

   `ifdef VCS

     property DSI_CMD_BUF_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_CMD_BUF_set !== 1'bx);
     endproperty
      as_DSI_CMD_BUF_set_not_x : assert property (DSI_CMD_BUF_set_not_x) else $error("Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_CMD_BUF_set is x after reset");
     cov_DSI_CMD_BUF_set_not_x :  cover property (DSI_CMD_BUF_set_not_x);

   `endif

   // ECC_CORR_IRQ_STAT : DSI_PDCM_DATA_BUF
   logic[1:0]  DSI_PDCM_DATA_BUF, DSI_PDCM_DATA_BUF_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DSI_PDCM_DATA_BUF <= 2'b0;
     end
     else begin
       DSI_PDCM_DATA_BUF <= DSI_PDCM_DATA_BUF_nxt;
     end
   end

   always_comb begin
     DSI_PDCM_DATA_BUF_nxt = DSI_PDCM_DATA_BUF;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[3:2])) begin
       DSI_PDCM_DATA_BUF_nxt = DSI_PDCM_DATA_BUF & (~data_in[3:2]);
     end
     if (Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_PDCM_DATA_BUF_set == 1'b1) begin
       DSI_PDCM_DATA_BUF_nxt = Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_PDCM_DATA_BUF_in;
     end
   end

   assign Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_PDCM_DATA_BUF = DSI_PDCM_DATA_BUF;

   `ifdef VCS

     property DSI_PDCM_DATA_BUF_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_PDCM_DATA_BUF_set !== 1'bx);
     endproperty
      as_DSI_PDCM_DATA_BUF_set_not_x : assert property (DSI_PDCM_DATA_BUF_set_not_x) else $error("Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_PDCM_DATA_BUF_set is x after reset");
     cov_DSI_PDCM_DATA_BUF_set_not_x :  cover property (DSI_PDCM_DATA_BUF_set_not_x);

   `endif

   // ECC_CORR_IRQ_STAT : DSI_CRM_DATA_BUF
   logic[1:0]  DSI_CRM_DATA_BUF, DSI_CRM_DATA_BUF_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DSI_CRM_DATA_BUF <= 2'b0;
     end
     else begin
       DSI_CRM_DATA_BUF <= DSI_CRM_DATA_BUF_nxt;
     end
   end

   always_comb begin
     DSI_CRM_DATA_BUF_nxt = DSI_CRM_DATA_BUF;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[1:0])) begin
       DSI_CRM_DATA_BUF_nxt = DSI_CRM_DATA_BUF & (~data_in[1:0]);
     end
     if (Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_CRM_DATA_BUF_set == 1'b1) begin
       DSI_CRM_DATA_BUF_nxt = Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_CRM_DATA_BUF_in;
     end
   end

   assign Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_CRM_DATA_BUF = DSI_CRM_DATA_BUF;

   `ifdef VCS

     property DSI_CRM_DATA_BUF_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_CRM_DATA_BUF_set !== 1'bx);
     endproperty
      as_DSI_CRM_DATA_BUF_set_not_x : assert property (DSI_CRM_DATA_BUF_set_not_x) else $error("Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_CRM_DATA_BUF_set is x after reset");
     cov_DSI_CRM_DATA_BUF_set_not_x :  cover property (DSI_CRM_DATA_BUF_set_not_x);

   `endif

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {RAM, SPI_DATA, SPI_CMD, SPI_CMD_BUF, 2'd0, DSI_CMD, DSI_TDMA, DSI_CMD_BUF, DSI_PDCM_DATA_BUF, DSI_CRM_DATA_BUF} : '0;

   assign Interrupt_Registers_ECC_CORR_IRQ_STAT.value = {RAM, SPI_DATA, SPI_CMD, SPI_CMD_BUF, 2'd0, DSI_CMD, DSI_TDMA, DSI_CMD_BUF, DSI_PDCM_DATA_BUF, DSI_CRM_DATA_BUF};

endmodule : Interrupt_Registers_ECC_CORR_IRQ_STAT

/*###   ECC_CORR_IRQ_MASK   ######################################################*/
module Interrupt_Registers_ECC_CORR_IRQ_MASK #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   Interrupt_Registers_ECC_CORR_IRQ_MASK_if.master Interrupt_Registers_ECC_CORR_IRQ_MASK);

   // ECC_CORR_IRQ_MASK : RAM
   logic  RAM, RAM_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       RAM <= 1'b1;
     end
     else begin
       RAM <= RAM_nxt;
     end
   end

   always_comb begin
     RAM_nxt = RAM;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       RAM_nxt = data_in[15:15]; 
     end
   end

   assign Interrupt_Registers_ECC_CORR_IRQ_MASK.RAM = RAM;

   // ECC_CORR_IRQ_MASK : SPI_DATA
   logic  SPI_DATA, SPI_DATA_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       SPI_DATA <= 1'b1;
     end
     else begin
       SPI_DATA <= SPI_DATA_nxt;
     end
   end

   always_comb begin
     SPI_DATA_nxt = SPI_DATA;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       SPI_DATA_nxt = data_in[14:14]; 
     end
   end

   assign Interrupt_Registers_ECC_CORR_IRQ_MASK.SPI_DATA = SPI_DATA;

   // ECC_CORR_IRQ_MASK : SPI_CMD
   logic  SPI_CMD, SPI_CMD_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       SPI_CMD <= 1'b1;
     end
     else begin
       SPI_CMD <= SPI_CMD_nxt;
     end
   end

   always_comb begin
     SPI_CMD_nxt = SPI_CMD;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       SPI_CMD_nxt = data_in[13:13]; 
     end
   end

   assign Interrupt_Registers_ECC_CORR_IRQ_MASK.SPI_CMD = SPI_CMD;

   // ECC_CORR_IRQ_MASK : SPI_CMD_BUF
   logic  SPI_CMD_BUF, SPI_CMD_BUF_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       SPI_CMD_BUF <= 1'b1;
     end
     else begin
       SPI_CMD_BUF <= SPI_CMD_BUF_nxt;
     end
   end

   always_comb begin
     SPI_CMD_BUF_nxt = SPI_CMD_BUF;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       SPI_CMD_BUF_nxt = data_in[12:12]; 
     end
   end

   assign Interrupt_Registers_ECC_CORR_IRQ_MASK.SPI_CMD_BUF = SPI_CMD_BUF;

   // ECC_CORR_IRQ_MASK : DSI_CMD
   logic[1:0]  DSI_CMD, DSI_CMD_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DSI_CMD <= 2'b11;
     end
     else begin
       DSI_CMD <= DSI_CMD_nxt;
     end
   end

   always_comb begin
     DSI_CMD_nxt = DSI_CMD;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       DSI_CMD_nxt = data_in[9:8]; 
     end
   end

   assign Interrupt_Registers_ECC_CORR_IRQ_MASK.DSI_CMD = DSI_CMD;

   // ECC_CORR_IRQ_MASK : DSI_TDMA
   logic[1:0]  DSI_TDMA, DSI_TDMA_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DSI_TDMA <= 2'b11;
     end
     else begin
       DSI_TDMA <= DSI_TDMA_nxt;
     end
   end

   always_comb begin
     DSI_TDMA_nxt = DSI_TDMA;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       DSI_TDMA_nxt = data_in[7:6]; 
     end
   end

   assign Interrupt_Registers_ECC_CORR_IRQ_MASK.DSI_TDMA = DSI_TDMA;

   // ECC_CORR_IRQ_MASK : DSI_CMD_BUF
   logic[1:0]  DSI_CMD_BUF, DSI_CMD_BUF_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DSI_CMD_BUF <= 2'b11;
     end
     else begin
       DSI_CMD_BUF <= DSI_CMD_BUF_nxt;
     end
   end

   always_comb begin
     DSI_CMD_BUF_nxt = DSI_CMD_BUF;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       DSI_CMD_BUF_nxt = data_in[5:4]; 
     end
   end

   assign Interrupt_Registers_ECC_CORR_IRQ_MASK.DSI_CMD_BUF = DSI_CMD_BUF;

   // ECC_CORR_IRQ_MASK : DSI_PDCM_DATA_BUF
   logic[1:0]  DSI_PDCM_DATA_BUF, DSI_PDCM_DATA_BUF_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DSI_PDCM_DATA_BUF <= 2'b11;
     end
     else begin
       DSI_PDCM_DATA_BUF <= DSI_PDCM_DATA_BUF_nxt;
     end
   end

   always_comb begin
     DSI_PDCM_DATA_BUF_nxt = DSI_PDCM_DATA_BUF;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       DSI_PDCM_DATA_BUF_nxt = data_in[3:2]; 
     end
   end

   assign Interrupt_Registers_ECC_CORR_IRQ_MASK.DSI_PDCM_DATA_BUF = DSI_PDCM_DATA_BUF;

   // ECC_CORR_IRQ_MASK : DSI_CRM_DATA_BUF
   logic[1:0]  DSI_CRM_DATA_BUF, DSI_CRM_DATA_BUF_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DSI_CRM_DATA_BUF <= 2'b11;
     end
     else begin
       DSI_CRM_DATA_BUF <= DSI_CRM_DATA_BUF_nxt;
     end
   end

   always_comb begin
     DSI_CRM_DATA_BUF_nxt = DSI_CRM_DATA_BUF;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       DSI_CRM_DATA_BUF_nxt = data_in[1:0]; 
     end
   end

   assign Interrupt_Registers_ECC_CORR_IRQ_MASK.DSI_CRM_DATA_BUF = DSI_CRM_DATA_BUF;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {RAM, SPI_DATA, SPI_CMD, SPI_CMD_BUF, 2'd0, DSI_CMD, DSI_TDMA, DSI_CMD_BUF, DSI_PDCM_DATA_BUF, DSI_CRM_DATA_BUF} : '0;

   assign Interrupt_Registers_ECC_CORR_IRQ_MASK.value = {RAM, SPI_DATA, SPI_CMD, SPI_CMD_BUF, 2'd0, DSI_CMD, DSI_TDMA, DSI_CMD_BUF, DSI_PDCM_DATA_BUF, DSI_CRM_DATA_BUF};

endmodule : Interrupt_Registers_ECC_CORR_IRQ_MASK

/*###   Registers   ######################################################*/
module Interrupt_Registers #(
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
   Interrupt_Registers_IRQ_STAT_if.master Interrupt_Registers_IRQ_STAT,
   Interrupt_Registers_IRQ_MASK_if.master Interrupt_Registers_IRQ_MASK,
   Interrupt_Registers_ECC_IRQ_STAT_if.master Interrupt_Registers_ECC_IRQ_STAT,
   Interrupt_Registers_ECC_IRQ_MASK_if.master Interrupt_Registers_ECC_IRQ_MASK,
   Interrupt_Registers_ECC_CORR_IRQ_STAT_if.master Interrupt_Registers_ECC_CORR_IRQ_STAT,
   Interrupt_Registers_ECC_CORR_IRQ_MASK_if.master Interrupt_Registers_ECC_CORR_IRQ_MASK
);

   logic[15:0] data_out_IRQ_STAT, data_out_IRQ_MASK, data_out_ECC_IRQ_STAT, data_out_ECC_IRQ_MASK, data_out_ECC_CORR_IRQ_STAT, data_out_ECC_CORR_IRQ_MASK;

   Interrupt_Registers_IRQ_STAT #( .reg_addr (base_addr + 'h50), .addr_width(addr_width) ) i_Interrupt_Registers_IRQ_STAT ( .data_out (data_out_IRQ_STAT), .*);
   Interrupt_Registers_IRQ_MASK #( .reg_addr (base_addr + 'h51), .addr_width(addr_width) ) i_Interrupt_Registers_IRQ_MASK ( .data_out (data_out_IRQ_MASK), .*);
   Interrupt_Registers_ECC_IRQ_STAT #( .reg_addr (base_addr + 'h52), .addr_width(addr_width) ) i_Interrupt_Registers_ECC_IRQ_STAT ( .data_out (data_out_ECC_IRQ_STAT), .*);
   Interrupt_Registers_ECC_IRQ_MASK #( .reg_addr (base_addr + 'h53), .addr_width(addr_width) ) i_Interrupt_Registers_ECC_IRQ_MASK ( .data_out (data_out_ECC_IRQ_MASK), .*);
   Interrupt_Registers_ECC_CORR_IRQ_STAT #( .reg_addr (base_addr + 'h54), .addr_width(addr_width) ) i_Interrupt_Registers_ECC_CORR_IRQ_STAT ( .data_out (data_out_ECC_CORR_IRQ_STAT), .*);
   Interrupt_Registers_ECC_CORR_IRQ_MASK #( .reg_addr (base_addr + 'h55), .addr_width(addr_width) ) i_Interrupt_Registers_ECC_CORR_IRQ_MASK ( .data_out (data_out_ECC_CORR_IRQ_MASK), .*);

   // output data assignment
   assign data_out = data_out_IRQ_STAT | data_out_IRQ_MASK | data_out_ECC_IRQ_STAT | data_out_ECC_IRQ_MASK | data_out_ECC_CORR_IRQ_STAT | data_out_ECC_CORR_IRQ_MASK;

endmodule : Interrupt_Registers
