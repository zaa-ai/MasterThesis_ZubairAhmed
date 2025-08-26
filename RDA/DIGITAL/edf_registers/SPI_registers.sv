/* ###   interfaces   ###################################################### */

// SPI_IRQ_STAT
interface SPI_registers_SPI_IRQ_STAT_if;
  logic[15:0] value;
  logic CMD_IGN, CMD_IGN_in;
  logic HW_FAIL, HW_FAIL_in;
  logic ALI_ERR, ALI_ERR_in;
  logic CRC_ERR, CRC_ERR_in;
  logic CMD_INC, CMD_INC_in;
  logic CMD_IGN_set, HW_FAIL_set, ALI_ERR_set, CRC_ERR_set, CMD_INC_set;

  modport master (
    input CMD_IGN_in, HW_FAIL_in, ALI_ERR_in, CRC_ERR_in, CMD_INC_in, CMD_IGN_set, HW_FAIL_set, ALI_ERR_set, CRC_ERR_set, CMD_INC_set, 
    output value, CMD_IGN, HW_FAIL, ALI_ERR, CRC_ERR, CMD_INC
  );

  modport slave (
    input value, CMD_IGN, HW_FAIL, ALI_ERR, CRC_ERR, CMD_INC, 
    output CMD_IGN_in, HW_FAIL_in, ALI_ERR_in, CRC_ERR_in, CMD_INC_in, CMD_IGN_set, HW_FAIL_set, ALI_ERR_set, CRC_ERR_set, CMD_INC_set
  );

endinterface : SPI_registers_SPI_IRQ_STAT_if

// SPI_IRQ_MASK
interface SPI_registers_SPI_IRQ_MASK_if;
  logic[15:0] value;
  logic CMD_IGN;
  logic HW_FAIL;
  logic ALI_ERR;
  logic CRC_ERR;
  logic CMD_INC;

  modport master (
    output value, CMD_IGN, HW_FAIL, ALI_ERR, CRC_ERR, CMD_INC
  );

  modport slave (
    input value, CMD_IGN, HW_FAIL, ALI_ERR, CRC_ERR, CMD_INC
  );

endinterface : SPI_registers_SPI_IRQ_MASK_if

// STATUS_WORD
interface SPI_registers_STATUS_WORD_if;
  logic[15:0] value;
  logic HE, HE_in;
  logic BF, BF_in;
  logic SCE, SCE_in;
  logic CRC, CRC_in;
  logic[1:0] NT, NT_in;
  logic[1:0] PD, PD_in;
  logic[1:0] CR, CR_in;

  modport master (
    input HE_in, BF_in, SCE_in, CRC_in, NT_in, PD_in, CR_in, 
    output value, HE, BF, SCE, CRC, NT, PD, CR
  );

  modport slave (
    input value, HE, BF, SCE, CRC, NT, PD, CR, 
    output HE_in, BF_in, SCE_in, CRC_in, NT_in, PD_in, CR_in
  );

endinterface : SPI_registers_STATUS_WORD_if



/*###   SPI_IRQ_STAT   ######################################################*/
module SPI_registers_SPI_IRQ_STAT #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   SPI_registers_SPI_IRQ_STAT_if.master SPI_registers_SPI_IRQ_STAT);

   // SPI_IRQ_STAT : CMD_IGN
   logic  CMD_IGN, CMD_IGN_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       CMD_IGN <= 1'b0;
     end
     else begin
       CMD_IGN <= CMD_IGN_nxt;
     end
   end

   always_comb begin
     CMD_IGN_nxt = CMD_IGN;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[4])) begin
       CMD_IGN_nxt = CMD_IGN & (~data_in[4]);
     end
     if (SPI_registers_SPI_IRQ_STAT.CMD_IGN_set == 1'b1) begin
       CMD_IGN_nxt = SPI_registers_SPI_IRQ_STAT.CMD_IGN_in;
     end
   end

   assign SPI_registers_SPI_IRQ_STAT.CMD_IGN = CMD_IGN;

   `ifdef VCS

     property CMD_IGN_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (SPI_registers_SPI_IRQ_STAT.CMD_IGN_set !== 1'bx);
     endproperty
      as_CMD_IGN_set_not_x : assert property (CMD_IGN_set_not_x) else $error("SPI_registers_SPI_IRQ_STAT.CMD_IGN_set is x after reset");
     cov_CMD_IGN_set_not_x :  cover property (CMD_IGN_set_not_x);

   `endif

   // SPI_IRQ_STAT : HW_FAIL
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
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[3])) begin
       HW_FAIL_nxt = HW_FAIL & (~data_in[3]);
     end
     if (SPI_registers_SPI_IRQ_STAT.HW_FAIL_set == 1'b1) begin
       HW_FAIL_nxt = SPI_registers_SPI_IRQ_STAT.HW_FAIL_in;
     end
   end

   assign SPI_registers_SPI_IRQ_STAT.HW_FAIL = HW_FAIL;

   `ifdef VCS

     property HW_FAIL_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (SPI_registers_SPI_IRQ_STAT.HW_FAIL_set !== 1'bx);
     endproperty
      as_HW_FAIL_set_not_x : assert property (HW_FAIL_set_not_x) else $error("SPI_registers_SPI_IRQ_STAT.HW_FAIL_set is x after reset");
     cov_HW_FAIL_set_not_x :  cover property (HW_FAIL_set_not_x);

   `endif

   // SPI_IRQ_STAT : ALI_ERR
   logic  ALI_ERR, ALI_ERR_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       ALI_ERR <= 1'b0;
     end
     else begin
       ALI_ERR <= ALI_ERR_nxt;
     end
   end

   always_comb begin
     ALI_ERR_nxt = ALI_ERR;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[2])) begin
       ALI_ERR_nxt = ALI_ERR & (~data_in[2]);
     end
     if (SPI_registers_SPI_IRQ_STAT.ALI_ERR_set == 1'b1) begin
       ALI_ERR_nxt = SPI_registers_SPI_IRQ_STAT.ALI_ERR_in;
     end
   end

   assign SPI_registers_SPI_IRQ_STAT.ALI_ERR = ALI_ERR;

   `ifdef VCS

     property ALI_ERR_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (SPI_registers_SPI_IRQ_STAT.ALI_ERR_set !== 1'bx);
     endproperty
      as_ALI_ERR_set_not_x : assert property (ALI_ERR_set_not_x) else $error("SPI_registers_SPI_IRQ_STAT.ALI_ERR_set is x after reset");
     cov_ALI_ERR_set_not_x :  cover property (ALI_ERR_set_not_x);

   `endif

   // SPI_IRQ_STAT : CRC_ERR
   logic  CRC_ERR, CRC_ERR_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       CRC_ERR <= 1'b0;
     end
     else begin
       CRC_ERR <= CRC_ERR_nxt;
     end
   end

   always_comb begin
     CRC_ERR_nxt = CRC_ERR;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[1])) begin
       CRC_ERR_nxt = CRC_ERR & (~data_in[1]);
     end
     if (SPI_registers_SPI_IRQ_STAT.CRC_ERR_set == 1'b1) begin
       CRC_ERR_nxt = SPI_registers_SPI_IRQ_STAT.CRC_ERR_in;
     end
   end

   assign SPI_registers_SPI_IRQ_STAT.CRC_ERR = CRC_ERR;

   `ifdef VCS

     property CRC_ERR_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (SPI_registers_SPI_IRQ_STAT.CRC_ERR_set !== 1'bx);
     endproperty
      as_CRC_ERR_set_not_x : assert property (CRC_ERR_set_not_x) else $error("SPI_registers_SPI_IRQ_STAT.CRC_ERR_set is x after reset");
     cov_CRC_ERR_set_not_x :  cover property (CRC_ERR_set_not_x);

   `endif

   // SPI_IRQ_STAT : CMD_INC
   logic  CMD_INC, CMD_INC_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       CMD_INC <= 1'b0;
     end
     else begin
       CMD_INC <= CMD_INC_nxt;
     end
   end

   always_comb begin
     CMD_INC_nxt = CMD_INC;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[0])) begin
       CMD_INC_nxt = CMD_INC & (~data_in[0]);
     end
     if (SPI_registers_SPI_IRQ_STAT.CMD_INC_set == 1'b1) begin
       CMD_INC_nxt = SPI_registers_SPI_IRQ_STAT.CMD_INC_in;
     end
   end

   assign SPI_registers_SPI_IRQ_STAT.CMD_INC = CMD_INC;

   `ifdef VCS

     property CMD_INC_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (SPI_registers_SPI_IRQ_STAT.CMD_INC_set !== 1'bx);
     endproperty
      as_CMD_INC_set_not_x : assert property (CMD_INC_set_not_x) else $error("SPI_registers_SPI_IRQ_STAT.CMD_INC_set is x after reset");
     cov_CMD_INC_set_not_x :  cover property (CMD_INC_set_not_x);

   `endif

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {11'd0, CMD_IGN, HW_FAIL, ALI_ERR, CRC_ERR, CMD_INC} : '0;

   assign SPI_registers_SPI_IRQ_STAT.value = {11'd0, CMD_IGN, HW_FAIL, ALI_ERR, CRC_ERR, CMD_INC};

endmodule : SPI_registers_SPI_IRQ_STAT

/*###   SPI_IRQ_MASK   ######################################################*/
module SPI_registers_SPI_IRQ_MASK #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   SPI_registers_SPI_IRQ_MASK_if.master SPI_registers_SPI_IRQ_MASK);

   // SPI_IRQ_MASK : CMD_IGN
   logic  CMD_IGN, CMD_IGN_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       CMD_IGN <= 1'b1;
     end
     else begin
       CMD_IGN <= CMD_IGN_nxt;
     end
   end

   always_comb begin
     CMD_IGN_nxt = CMD_IGN;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       CMD_IGN_nxt = data_in[4:4]; 
     end
   end

   assign SPI_registers_SPI_IRQ_MASK.CMD_IGN = CMD_IGN;

   // SPI_IRQ_MASK : HW_FAIL
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
       HW_FAIL_nxt = data_in[3:3]; 
     end
   end

   assign SPI_registers_SPI_IRQ_MASK.HW_FAIL = HW_FAIL;

   // SPI_IRQ_MASK : ALI_ERR
   logic  ALI_ERR, ALI_ERR_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       ALI_ERR <= 1'b1;
     end
     else begin
       ALI_ERR <= ALI_ERR_nxt;
     end
   end

   always_comb begin
     ALI_ERR_nxt = ALI_ERR;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       ALI_ERR_nxt = data_in[2:2]; 
     end
   end

   assign SPI_registers_SPI_IRQ_MASK.ALI_ERR = ALI_ERR;

   // SPI_IRQ_MASK : CRC_ERR
   logic  CRC_ERR, CRC_ERR_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       CRC_ERR <= 1'b1;
     end
     else begin
       CRC_ERR <= CRC_ERR_nxt;
     end
   end

   always_comb begin
     CRC_ERR_nxt = CRC_ERR;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       CRC_ERR_nxt = data_in[1:1]; 
     end
   end

   assign SPI_registers_SPI_IRQ_MASK.CRC_ERR = CRC_ERR;

   // SPI_IRQ_MASK : CMD_INC
   logic  CMD_INC, CMD_INC_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       CMD_INC <= 1'b1;
     end
     else begin
       CMD_INC <= CMD_INC_nxt;
     end
   end

   always_comb begin
     CMD_INC_nxt = CMD_INC;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       CMD_INC_nxt = data_in[0:0]; 
     end
   end

   assign SPI_registers_SPI_IRQ_MASK.CMD_INC = CMD_INC;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {11'd0, CMD_IGN, HW_FAIL, ALI_ERR, CRC_ERR, CMD_INC} : '0;

   assign SPI_registers_SPI_IRQ_MASK.value = {11'd0, CMD_IGN, HW_FAIL, ALI_ERR, CRC_ERR, CMD_INC};

endmodule : SPI_registers_SPI_IRQ_MASK

/*###   STATUS_WORD   ######################################################*/
module SPI_registers_STATUS_WORD #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   input logic[addr_width-1:0] addr,
   input logic           rd,
   output logic[15:0]     data_out,
   SPI_registers_STATUS_WORD_if.master SPI_registers_STATUS_WORD);

   // STATUS_WORD : HE
   logic  HE;


   always_comb begin
       HE = SPI_registers_STATUS_WORD.HE_in;
   end

   assign SPI_registers_STATUS_WORD.HE = HE;

   // STATUS_WORD : BF
   logic  BF;


   always_comb begin
       BF = SPI_registers_STATUS_WORD.BF_in;
   end

   assign SPI_registers_STATUS_WORD.BF = BF;

   // STATUS_WORD : SCE
   logic  SCE;


   always_comb begin
       SCE = SPI_registers_STATUS_WORD.SCE_in;
   end

   assign SPI_registers_STATUS_WORD.SCE = SCE;

   // STATUS_WORD : CRC
   logic  CRC;


   always_comb begin
       CRC = SPI_registers_STATUS_WORD.CRC_in;
   end

   assign SPI_registers_STATUS_WORD.CRC = CRC;

   // STATUS_WORD : NT
   logic[1:0]  NT;


   always_comb begin
       NT = SPI_registers_STATUS_WORD.NT_in;
   end

   assign SPI_registers_STATUS_WORD.NT = NT;

   // STATUS_WORD : PD
   logic[1:0]  PD;


   always_comb begin
       PD = SPI_registers_STATUS_WORD.PD_in;
   end

   assign SPI_registers_STATUS_WORD.PD = PD;

   // STATUS_WORD : CR
   logic[1:0]  CR;


   always_comb begin
       CR = SPI_registers_STATUS_WORD.CR_in;
   end

   assign SPI_registers_STATUS_WORD.CR = CR;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {HE, BF, SCE, CRC, NT, 6'd0, PD, CR} : '0;

   assign SPI_registers_STATUS_WORD.value = {HE, BF, SCE, CRC, NT, 6'd0, PD, CR};

endmodule : SPI_registers_STATUS_WORD

/*###   Registers   ######################################################*/
module SPI_registers #(
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
   SPI_registers_SPI_IRQ_STAT_if.master SPI_registers_SPI_IRQ_STAT,
   SPI_registers_SPI_IRQ_MASK_if.master SPI_registers_SPI_IRQ_MASK,
   SPI_registers_STATUS_WORD_if.master SPI_registers_STATUS_WORD
);

   logic[15:0] data_out_SPI_IRQ_STAT, data_out_SPI_IRQ_MASK, data_out_STATUS_WORD;

   SPI_registers_SPI_IRQ_STAT #( .reg_addr (base_addr + 'h80), .addr_width(addr_width) ) i_SPI_registers_SPI_IRQ_STAT ( .data_out (data_out_SPI_IRQ_STAT), .*);
   SPI_registers_SPI_IRQ_MASK #( .reg_addr (base_addr + 'h81), .addr_width(addr_width) ) i_SPI_registers_SPI_IRQ_MASK ( .data_out (data_out_SPI_IRQ_MASK), .*);
   SPI_registers_STATUS_WORD #( .reg_addr (base_addr + 'h85), .addr_width(addr_width) ) i_SPI_registers_STATUS_WORD ( .data_out (data_out_STATUS_WORD), .*);

   // output data assignment
   assign data_out = data_out_SPI_IRQ_STAT | data_out_SPI_IRQ_MASK | data_out_STATUS_WORD;

endmodule : SPI_registers
