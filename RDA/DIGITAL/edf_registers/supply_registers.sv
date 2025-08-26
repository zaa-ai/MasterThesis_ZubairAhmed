/* ###   interfaces   ###################################################### */

// TRIM_IREF
interface supply_registers_TRIM_IREF_if;
  logic[15:0] value;
  logic[3:0] IREF;

  modport master (
    output value, IREF
  );

  modport slave (
    input value, IREF
  );

endinterface : supply_registers_TRIM_IREF_if

// TRIM_OT
interface supply_registers_TRIM_OT_if;
  logic[15:0] value;
  logic[1:0] TRIM_OT;

  modport master (
    output value, TRIM_OT
  );

  modport slave (
    input value, TRIM_OT
  );

endinterface : supply_registers_TRIM_OT_if

// SUP_IRQ_STAT
interface supply_registers_SUP_IRQ_STAT_if;
  logic[15:0] value;
  logic OTW, OTW_in;
  logic OTE, OTE_in;
  logic LDOUV, LDOUV_in;
  logic VCCUV, VCCUV_in;
  logic REF_FAIL, REF_FAIL_in;
  logic OTW_set, OTE_set, LDOUV_set, VCCUV_set, REF_FAIL_set;

  modport master (
    input OTW_in, OTE_in, LDOUV_in, VCCUV_in, REF_FAIL_in, OTW_set, OTE_set, LDOUV_set, VCCUV_set, REF_FAIL_set, 
    output value, OTW, OTE, LDOUV, VCCUV, REF_FAIL
  );

  modport slave (
    input value, OTW, OTE, LDOUV, VCCUV, REF_FAIL, 
    output OTW_in, OTE_in, LDOUV_in, VCCUV_in, REF_FAIL_in, OTW_set, OTE_set, LDOUV_set, VCCUV_set, REF_FAIL_set
  );

endinterface : supply_registers_SUP_IRQ_STAT_if

// SUP_IRQ_MASK
interface supply_registers_SUP_IRQ_MASK_if;
  logic[15:0] value;
  logic OTW;
  logic OTE;
  logic LDOUV;
  logic VCCUV;
  logic REF_FAIL;

  modport master (
    output value, OTW, OTE, LDOUV, VCCUV, REF_FAIL
  );

  modport slave (
    input value, OTW, OTE, LDOUV, VCCUV, REF_FAIL
  );

endinterface : supply_registers_SUP_IRQ_MASK_if

// SUP_HW_CTRL
interface supply_registers_SUP_HW_CTRL_if;
  logic[15:0] value;
  logic IGNORE_HWF;
  logic IGNORE_UV;

  modport master (
    output value, IGNORE_HWF, IGNORE_UV
  );

  modport slave (
    input value, IGNORE_HWF, IGNORE_UV
  );

endinterface : supply_registers_SUP_HW_CTRL_if

// SUP_STAT
interface supply_registers_SUP_STAT_if;
  logic[15:0] value;
  logic OTW, OTW_in;
  logic OTE, OTE_in;
  logic LDOUV, LDOUV_in;
  logic VCCUV, VCCUV_in;
  logic REF_FAIL, REF_FAIL_in;

  modport master (
    input OTW_in, OTE_in, LDOUV_in, VCCUV_in, REF_FAIL_in, 
    output value, OTW, OTE, LDOUV, VCCUV, REF_FAIL
  );

  modport slave (
    input value, OTW, OTE, LDOUV, VCCUV, REF_FAIL, 
    output OTW_in, OTE_in, LDOUV_in, VCCUV_in, REF_FAIL_in
  );

endinterface : supply_registers_SUP_STAT_if

// SUP_CTRL
interface supply_registers_SUP_CTRL_if;
  logic[15:0] value;
  logic EN_LDO, EN_LDO_in;
  logic EN_LDO_set;

  modport master (
    input EN_LDO_in, EN_LDO_set, 
    output value, EN_LDO
  );

  modport slave (
    input value, EN_LDO, 
    output EN_LDO_in, EN_LDO_set
  );

endinterface : supply_registers_SUP_CTRL_if

// IO_CTRL
interface supply_registers_IO_CTRL_if;
  logic[15:0] value;
  logic HICUR;

  modport master (
    output value, HICUR
  );

  modport slave (
    input value, HICUR
  );

endinterface : supply_registers_IO_CTRL_if



/*###   TRIM_IREF   ######################################################*/
module supply_registers_TRIM_IREF #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   supply_registers_TRIM_IREF_if.master supply_registers_TRIM_IREF);

   // TRIM_IREF : IREF
   logic[3:0]  IREF, IREF_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       IREF <= 4'b0;
     end
     else begin
       IREF <= IREF_nxt;
     end
   end

   always_comb begin
     IREF_nxt = IREF;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       IREF_nxt = data_in[3:0]; 
     end
   end

   assign supply_registers_TRIM_IREF.IREF = IREF;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {12'd0, IREF} : '0;

   assign supply_registers_TRIM_IREF.value = {12'd0, IREF};

endmodule : supply_registers_TRIM_IREF

/*###   TRIM_OT   ######################################################*/
module supply_registers_TRIM_OT #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   supply_registers_TRIM_OT_if.master supply_registers_TRIM_OT);

   // TRIM_OT : TRIM_OT
   logic[1:0]  TRIM_OT, TRIM_OT_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       TRIM_OT <= 2'b0;
     end
     else begin
       TRIM_OT <= TRIM_OT_nxt;
     end
   end

   always_comb begin
     TRIM_OT_nxt = TRIM_OT;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       TRIM_OT_nxt = data_in[1:0]; 
     end
   end

   assign supply_registers_TRIM_OT.TRIM_OT = TRIM_OT;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {14'd0, TRIM_OT} : '0;

   assign supply_registers_TRIM_OT.value = {14'd0, TRIM_OT};

endmodule : supply_registers_TRIM_OT

/*###   SUP_IRQ_STAT   ######################################################*/
module supply_registers_SUP_IRQ_STAT #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   supply_registers_SUP_IRQ_STAT_if.master supply_registers_SUP_IRQ_STAT);

   // SUP_IRQ_STAT : OTW
   logic  OTW, OTW_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       OTW <= 1'b0;
     end
     else begin
       OTW <= OTW_nxt;
     end
   end

   always_comb begin
     OTW_nxt = OTW;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[4])) begin
       OTW_nxt = OTW & (~data_in[4]);
     end
     if (supply_registers_SUP_IRQ_STAT.OTW_set == 1'b1) begin
       OTW_nxt = supply_registers_SUP_IRQ_STAT.OTW_in;
     end
   end

   assign supply_registers_SUP_IRQ_STAT.OTW = OTW;

   `ifdef VCS

     property OTW_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (supply_registers_SUP_IRQ_STAT.OTW_set !== 1'bx);
     endproperty
      as_OTW_set_not_x : assert property (OTW_set_not_x) else $error("supply_registers_SUP_IRQ_STAT.OTW_set is x after reset");
     cov_OTW_set_not_x :  cover property (OTW_set_not_x);

   `endif

   // SUP_IRQ_STAT : OTE
   logic  OTE, OTE_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       OTE <= 1'b0;
     end
     else begin
       OTE <= OTE_nxt;
     end
   end

   always_comb begin
     OTE_nxt = OTE;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[3])) begin
       OTE_nxt = OTE & (~data_in[3]);
     end
     if (supply_registers_SUP_IRQ_STAT.OTE_set == 1'b1) begin
       OTE_nxt = supply_registers_SUP_IRQ_STAT.OTE_in;
     end
   end

   assign supply_registers_SUP_IRQ_STAT.OTE = OTE;

   `ifdef VCS

     property OTE_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (supply_registers_SUP_IRQ_STAT.OTE_set !== 1'bx);
     endproperty
      as_OTE_set_not_x : assert property (OTE_set_not_x) else $error("supply_registers_SUP_IRQ_STAT.OTE_set is x after reset");
     cov_OTE_set_not_x :  cover property (OTE_set_not_x);

   `endif

   // SUP_IRQ_STAT : LDOUV
   logic  LDOUV, LDOUV_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       LDOUV <= 1'b0;
     end
     else begin
       LDOUV <= LDOUV_nxt;
     end
   end

   always_comb begin
     LDOUV_nxt = LDOUV;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[2])) begin
       LDOUV_nxt = LDOUV & (~data_in[2]);
     end
     if (supply_registers_SUP_IRQ_STAT.LDOUV_set == 1'b1) begin
       LDOUV_nxt = supply_registers_SUP_IRQ_STAT.LDOUV_in;
     end
   end

   assign supply_registers_SUP_IRQ_STAT.LDOUV = LDOUV;

   `ifdef VCS

     property LDOUV_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (supply_registers_SUP_IRQ_STAT.LDOUV_set !== 1'bx);
     endproperty
      as_LDOUV_set_not_x : assert property (LDOUV_set_not_x) else $error("supply_registers_SUP_IRQ_STAT.LDOUV_set is x after reset");
     cov_LDOUV_set_not_x :  cover property (LDOUV_set_not_x);

   `endif

   // SUP_IRQ_STAT : VCCUV
   logic  VCCUV, VCCUV_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       VCCUV <= 1'b0;
     end
     else begin
       VCCUV <= VCCUV_nxt;
     end
   end

   always_comb begin
     VCCUV_nxt = VCCUV;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[1])) begin
       VCCUV_nxt = VCCUV & (~data_in[1]);
     end
     if (supply_registers_SUP_IRQ_STAT.VCCUV_set == 1'b1) begin
       VCCUV_nxt = supply_registers_SUP_IRQ_STAT.VCCUV_in;
     end
   end

   assign supply_registers_SUP_IRQ_STAT.VCCUV = VCCUV;

   `ifdef VCS

     property VCCUV_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (supply_registers_SUP_IRQ_STAT.VCCUV_set !== 1'bx);
     endproperty
      as_VCCUV_set_not_x : assert property (VCCUV_set_not_x) else $error("supply_registers_SUP_IRQ_STAT.VCCUV_set is x after reset");
     cov_VCCUV_set_not_x :  cover property (VCCUV_set_not_x);

   `endif

   // SUP_IRQ_STAT : REF_FAIL
   logic  REF_FAIL, REF_FAIL_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       REF_FAIL <= 1'b0;
     end
     else begin
       REF_FAIL <= REF_FAIL_nxt;
     end
   end

   always_comb begin
     REF_FAIL_nxt = REF_FAIL;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[0])) begin
       REF_FAIL_nxt = REF_FAIL & (~data_in[0]);
     end
     if (supply_registers_SUP_IRQ_STAT.REF_FAIL_set == 1'b1) begin
       REF_FAIL_nxt = supply_registers_SUP_IRQ_STAT.REF_FAIL_in;
     end
   end

   assign supply_registers_SUP_IRQ_STAT.REF_FAIL = REF_FAIL;

   `ifdef VCS

     property REF_FAIL_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (supply_registers_SUP_IRQ_STAT.REF_FAIL_set !== 1'bx);
     endproperty
      as_REF_FAIL_set_not_x : assert property (REF_FAIL_set_not_x) else $error("supply_registers_SUP_IRQ_STAT.REF_FAIL_set is x after reset");
     cov_REF_FAIL_set_not_x :  cover property (REF_FAIL_set_not_x);

   `endif

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {11'd0, OTW, OTE, LDOUV, VCCUV, REF_FAIL} : '0;

   assign supply_registers_SUP_IRQ_STAT.value = {11'd0, OTW, OTE, LDOUV, VCCUV, REF_FAIL};

endmodule : supply_registers_SUP_IRQ_STAT

/*###   SUP_IRQ_MASK   ######################################################*/
module supply_registers_SUP_IRQ_MASK #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   supply_registers_SUP_IRQ_MASK_if.master supply_registers_SUP_IRQ_MASK);

   // SUP_IRQ_MASK : OTW
   logic  OTW, OTW_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       OTW <= 1'b1;
     end
     else begin
       OTW <= OTW_nxt;
     end
   end

   always_comb begin
     OTW_nxt = OTW;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       OTW_nxt = data_in[4:4]; 
     end
   end

   assign supply_registers_SUP_IRQ_MASK.OTW = OTW;

   // SUP_IRQ_MASK : OTE
   logic  OTE, OTE_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       OTE <= 1'b1;
     end
     else begin
       OTE <= OTE_nxt;
     end
   end

   always_comb begin
     OTE_nxt = OTE;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       OTE_nxt = data_in[3:3]; 
     end
   end

   assign supply_registers_SUP_IRQ_MASK.OTE = OTE;

   // SUP_IRQ_MASK : LDOUV
   logic  LDOUV, LDOUV_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       LDOUV <= 1'b1;
     end
     else begin
       LDOUV <= LDOUV_nxt;
     end
   end

   always_comb begin
     LDOUV_nxt = LDOUV;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       LDOUV_nxt = data_in[2:2]; 
     end
   end

   assign supply_registers_SUP_IRQ_MASK.LDOUV = LDOUV;

   // SUP_IRQ_MASK : VCCUV
   logic  VCCUV, VCCUV_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       VCCUV <= 1'b1;
     end
     else begin
       VCCUV <= VCCUV_nxt;
     end
   end

   always_comb begin
     VCCUV_nxt = VCCUV;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       VCCUV_nxt = data_in[1:1]; 
     end
   end

   assign supply_registers_SUP_IRQ_MASK.VCCUV = VCCUV;

   // SUP_IRQ_MASK : REF_FAIL
   logic  REF_FAIL, REF_FAIL_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       REF_FAIL <= 1'b1;
     end
     else begin
       REF_FAIL <= REF_FAIL_nxt;
     end
   end

   always_comb begin
     REF_FAIL_nxt = REF_FAIL;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       REF_FAIL_nxt = data_in[0:0]; 
     end
   end

   assign supply_registers_SUP_IRQ_MASK.REF_FAIL = REF_FAIL;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {11'd0, OTW, OTE, LDOUV, VCCUV, REF_FAIL} : '0;

   assign supply_registers_SUP_IRQ_MASK.value = {11'd0, OTW, OTE, LDOUV, VCCUV, REF_FAIL};

endmodule : supply_registers_SUP_IRQ_MASK

/*###   SUP_HW_CTRL   ######################################################*/
module supply_registers_SUP_HW_CTRL #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   supply_registers_SUP_HW_CTRL_if.master supply_registers_SUP_HW_CTRL);

   // SUP_HW_CTRL : IGNORE_HWF
   logic  IGNORE_HWF, IGNORE_HWF_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       IGNORE_HWF <= 1'b0;
     end
     else begin
       IGNORE_HWF <= IGNORE_HWF_nxt;
     end
   end

   always_comb begin
     IGNORE_HWF_nxt = IGNORE_HWF;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       IGNORE_HWF_nxt = data_in[1:1]; 
     end
   end

   assign supply_registers_SUP_HW_CTRL.IGNORE_HWF = IGNORE_HWF;

   // SUP_HW_CTRL : IGNORE_UV
   logic  IGNORE_UV, IGNORE_UV_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       IGNORE_UV <= 1'b0;
     end
     else begin
       IGNORE_UV <= IGNORE_UV_nxt;
     end
   end

   always_comb begin
     IGNORE_UV_nxt = IGNORE_UV;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       IGNORE_UV_nxt = data_in[0:0]; 
     end
   end

   assign supply_registers_SUP_HW_CTRL.IGNORE_UV = IGNORE_UV;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {14'd0, IGNORE_HWF, IGNORE_UV} : '0;

   assign supply_registers_SUP_HW_CTRL.value = {14'd0, IGNORE_HWF, IGNORE_UV};

endmodule : supply_registers_SUP_HW_CTRL

/*###   SUP_STAT   ######################################################*/
module supply_registers_SUP_STAT #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   input logic[addr_width-1:0] addr,
   input logic           rd,
   output logic[15:0]     data_out,
   supply_registers_SUP_STAT_if.master supply_registers_SUP_STAT);

   // SUP_STAT : OTW
   logic  OTW;


   always_comb begin
       OTW = supply_registers_SUP_STAT.OTW_in;
   end

   assign supply_registers_SUP_STAT.OTW = OTW;

   // SUP_STAT : OTE
   logic  OTE;


   always_comb begin
       OTE = supply_registers_SUP_STAT.OTE_in;
   end

   assign supply_registers_SUP_STAT.OTE = OTE;

   // SUP_STAT : LDOUV
   logic  LDOUV;


   always_comb begin
       LDOUV = supply_registers_SUP_STAT.LDOUV_in;
   end

   assign supply_registers_SUP_STAT.LDOUV = LDOUV;

   // SUP_STAT : VCCUV
   logic  VCCUV;


   always_comb begin
       VCCUV = supply_registers_SUP_STAT.VCCUV_in;
   end

   assign supply_registers_SUP_STAT.VCCUV = VCCUV;

   // SUP_STAT : REF_FAIL
   logic  REF_FAIL;


   always_comb begin
       REF_FAIL = supply_registers_SUP_STAT.REF_FAIL_in;
   end

   assign supply_registers_SUP_STAT.REF_FAIL = REF_FAIL;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {11'd0, OTW, OTE, LDOUV, VCCUV, REF_FAIL} : '0;

   assign supply_registers_SUP_STAT.value = {11'd0, OTW, OTE, LDOUV, VCCUV, REF_FAIL};

endmodule : supply_registers_SUP_STAT

/*###   SUP_CTRL   ######################################################*/
module supply_registers_SUP_CTRL #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   supply_registers_SUP_CTRL_if.master supply_registers_SUP_CTRL);

   // SUP_CTRL : EN_LDO
   logic  EN_LDO, EN_LDO_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       EN_LDO <= 1'b1;
     end
     else begin
       EN_LDO <= EN_LDO_nxt;
     end
   end

   always_comb begin
     EN_LDO_nxt = EN_LDO;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       EN_LDO_nxt = data_in[0:0]; 
     end
     if (supply_registers_SUP_CTRL.EN_LDO_set == 1'b1) begin
       EN_LDO_nxt = supply_registers_SUP_CTRL.EN_LDO_in;
     end
   end

   assign supply_registers_SUP_CTRL.EN_LDO = EN_LDO;

   `ifdef VCS

     property EN_LDO_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (supply_registers_SUP_CTRL.EN_LDO_set !== 1'bx);
     endproperty
      as_EN_LDO_set_not_x : assert property (EN_LDO_set_not_x) else $error("supply_registers_SUP_CTRL.EN_LDO_set is x after reset");
     cov_EN_LDO_set_not_x :  cover property (EN_LDO_set_not_x);

   `endif

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {15'd0, EN_LDO} : '0;

   assign supply_registers_SUP_CTRL.value = {15'd0, EN_LDO};

endmodule : supply_registers_SUP_CTRL

/*###   IO_CTRL   ######################################################*/
module supply_registers_IO_CTRL #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   supply_registers_IO_CTRL_if.master supply_registers_IO_CTRL);

   // IO_CTRL : HICUR
   logic  HICUR, HICUR_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       HICUR <= 1'b1;
     end
     else begin
       HICUR <= HICUR_nxt;
     end
   end

   always_comb begin
     HICUR_nxt = HICUR;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       HICUR_nxt = data_in[0:0]; 
     end
   end

   assign supply_registers_IO_CTRL.HICUR = HICUR;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {15'd0, HICUR} : '0;

   assign supply_registers_IO_CTRL.value = {15'd0, HICUR};

endmodule : supply_registers_IO_CTRL

/*###   Registers   ######################################################*/
module supply_registers #(
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
   supply_registers_TRIM_IREF_if.master supply_registers_TRIM_IREF,
   supply_registers_TRIM_OT_if.master supply_registers_TRIM_OT,
   supply_registers_SUP_IRQ_STAT_if.master supply_registers_SUP_IRQ_STAT,
   supply_registers_SUP_IRQ_MASK_if.master supply_registers_SUP_IRQ_MASK,
   supply_registers_SUP_HW_CTRL_if.master supply_registers_SUP_HW_CTRL,
   supply_registers_SUP_STAT_if.master supply_registers_SUP_STAT,
   supply_registers_SUP_CTRL_if.master supply_registers_SUP_CTRL,
   supply_registers_IO_CTRL_if.master supply_registers_IO_CTRL
);

   logic[15:0] data_out_TRIM_IREF, data_out_TRIM_OT, data_out_SUP_IRQ_STAT, data_out_SUP_IRQ_MASK, data_out_SUP_HW_CTRL, data_out_SUP_STAT, data_out_SUP_CTRL, data_out_IO_CTRL;

   supply_registers_TRIM_IREF #( .reg_addr (base_addr + 'h3), .addr_width(addr_width) ) i_supply_registers_TRIM_IREF ( .data_out (data_out_TRIM_IREF), .*);
   supply_registers_TRIM_OT #( .reg_addr (base_addr + 'h4), .addr_width(addr_width) ) i_supply_registers_TRIM_OT ( .data_out (data_out_TRIM_OT), .*);
   supply_registers_SUP_IRQ_STAT #( .reg_addr (base_addr + 'h3a), .addr_width(addr_width) ) i_supply_registers_SUP_IRQ_STAT ( .data_out (data_out_SUP_IRQ_STAT), .*);
   supply_registers_SUP_IRQ_MASK #( .reg_addr (base_addr + 'h3b), .addr_width(addr_width) ) i_supply_registers_SUP_IRQ_MASK ( .data_out (data_out_SUP_IRQ_MASK), .*);
   supply_registers_SUP_HW_CTRL #( .reg_addr (base_addr + 'h3c), .addr_width(addr_width) ) i_supply_registers_SUP_HW_CTRL ( .data_out (data_out_SUP_HW_CTRL), .*);
   supply_registers_SUP_STAT #( .reg_addr (base_addr + 'h3d), .addr_width(addr_width) ) i_supply_registers_SUP_STAT ( .data_out (data_out_SUP_STAT), .*);
   supply_registers_SUP_CTRL #( .reg_addr (base_addr + 'h3e), .addr_width(addr_width) ) i_supply_registers_SUP_CTRL ( .data_out (data_out_SUP_CTRL), .*);
   supply_registers_IO_CTRL #( .reg_addr (base_addr + 'h3f), .addr_width(addr_width) ) i_supply_registers_IO_CTRL ( .data_out (data_out_IO_CTRL), .*);

   // output data assignment
   assign data_out = data_out_TRIM_IREF | data_out_TRIM_OT | data_out_SUP_IRQ_STAT | data_out_SUP_IRQ_MASK | data_out_SUP_HW_CTRL | data_out_SUP_STAT | data_out_SUP_CTRL | data_out_IO_CTRL;

endmodule : supply_registers
