/* ###   interfaces   ###################################################### */

// DSI_STAT
interface DSI3_channel_registers_DSI_STAT_if;
  logic[15:0] value;
  logic[3:0] SLAVES, SLAVES_in;
  logic SYNC, SYNC_in;
  logic DSIUV, DSIUV_in;
  logic DSIOV, DSIOV_in;
  logic[7:0] PULSECNT, PULSECNT_in;

  modport master (
    input SLAVES_in, SYNC_in, DSIUV_in, DSIOV_in, PULSECNT_in, 
    output value, SLAVES, SYNC, DSIUV, DSIOV, PULSECNT
  );

  modport slave (
    input value, SLAVES, SYNC, DSIUV, DSIOV, PULSECNT, 
    output SLAVES_in, SYNC_in, DSIUV_in, DSIOV_in, PULSECNT_in
  );

endinterface : DSI3_channel_registers_DSI_STAT_if

// PDCM_PERIOD
interface DSI3_channel_registers_PDCM_PERIOD_if;
  logic[15:0] value;
  logic access_rd;
  logic[15:0] PDCMPER, PDCMPER_in;
  logic PDCMPER_set;

  modport master (
    input PDCMPER_in, PDCMPER_set, 
    output value, access_rd, PDCMPER
  );

  modport slave (
    input value, access_rd, PDCMPER, 
    output PDCMPER_in, PDCMPER_set
  );

endinterface : DSI3_channel_registers_PDCM_PERIOD_if

// DSI_LOAD
interface DSI3_channel_registers_DSI_LOAD_if;
  logic[15:0] value;
  logic START_MEASUREMENT, START_MEASUREMENT_in;
  logic IDLE, IDLE_in;
  logic[4:0] LOAD, LOAD_in;
  logic START_MEASUREMENT_set, IDLE_set, LOAD_set;

  modport master (
    input START_MEASUREMENT_in, IDLE_in, LOAD_in, START_MEASUREMENT_set, IDLE_set, LOAD_set, 
    output value, START_MEASUREMENT, IDLE, LOAD
  );

  modport slave (
    input value, START_MEASUREMENT, IDLE, LOAD, 
    output START_MEASUREMENT_in, IDLE_in, LOAD_in, START_MEASUREMENT_set, IDLE_set, LOAD_set
  );

endinterface : DSI3_channel_registers_DSI_LOAD_if

// DSI_IRQ_STAT
interface DSI3_channel_registers_DSI_IRQ_STAT_if;
  logic[15:0] value;
  logic IQ_ERR, IQ_ERR_in;
  logic COM_ERR, COM_ERR_in;
  logic DMOF, DMOF_in;
  logic HW_FAIL, HW_FAIL_in;
  logic SYNC_ERR, SYNC_ERR_in;
  logic DSIUV, DSIUV_in;
  logic DSIOV, DSIOV_in;
  logic IQ_ERR_set, COM_ERR_set, DMOF_set, HW_FAIL_set, SYNC_ERR_set, DSIUV_set, DSIOV_set;

  modport master (
    input IQ_ERR_in, COM_ERR_in, DMOF_in, HW_FAIL_in, SYNC_ERR_in, DSIUV_in, DSIOV_in, IQ_ERR_set, COM_ERR_set, DMOF_set, HW_FAIL_set, SYNC_ERR_set, DSIUV_set, DSIOV_set, 
    output value, IQ_ERR, COM_ERR, DMOF, HW_FAIL, SYNC_ERR, DSIUV, DSIOV
  );

  modport slave (
    input value, IQ_ERR, COM_ERR, DMOF, HW_FAIL, SYNC_ERR, DSIUV, DSIOV, 
    output IQ_ERR_in, COM_ERR_in, DMOF_in, HW_FAIL_in, SYNC_ERR_in, DSIUV_in, DSIOV_in, IQ_ERR_set, COM_ERR_set, DMOF_set, HW_FAIL_set, SYNC_ERR_set, DSIUV_set, DSIOV_set
  );

endinterface : DSI3_channel_registers_DSI_IRQ_STAT_if

// DSI_IRQ_MASK
interface DSI3_channel_registers_DSI_IRQ_MASK_if;
  logic[15:0] value;
  logic IQ_ERR;
  logic COM_ERR;
  logic DMOF;
  logic HW_FAIL;
  logic SYNC_ERR;
  logic DSIUV;
  logic DSIOV;

  modport master (
    output value, IQ_ERR, COM_ERR, DMOF, HW_FAIL, SYNC_ERR, DSIUV, DSIOV
  );

  modport slave (
    input value, IQ_ERR, COM_ERR, DMOF, HW_FAIL, SYNC_ERR, DSIUV, DSIOV
  );

endinterface : DSI3_channel_registers_DSI_IRQ_MASK_if

// DSI_CMD
interface DSI3_channel_registers_DSI_CMD_if;
  logic[15:0] value;
  logic[3:0] CMD, CMD_in;
  logic[11:0] DATA, DATA_in;

  modport master (
    input CMD_in, DATA_in, 
    output value, CMD, DATA
  );

  modport slave (
    input value, CMD, DATA, 
    output CMD_in, DATA_in
  );

endinterface : DSI3_channel_registers_DSI_CMD_if

// CRM_WORD2
interface DSI3_channel_registers_CRM_WORD2_if;
  logic[15:0] value;
  logic[15:0] CRM_WORD2, CRM_WORD2_in;

  modport master (
    input CRM_WORD2_in, 
    output value, CRM_WORD2
  );

  modport slave (
    input value, CRM_WORD2, 
    output CRM_WORD2_in
  );

endinterface : DSI3_channel_registers_CRM_WORD2_if

// CRM_WORD1
interface DSI3_channel_registers_CRM_WORD1_if;
  logic[15:0] value;
  logic[15:0] CRM_WORD1, CRM_WORD1_in;

  modport master (
    input CRM_WORD1_in, 
    output value, CRM_WORD1
  );

  modport slave (
    input value, CRM_WORD1, 
    output CRM_WORD1_in
  );

endinterface : DSI3_channel_registers_CRM_WORD1_if

// PACKET_STAT
interface DSI3_channel_registers_PACKET_STAT_if;
  logic[15:0] value;
  logic SCE, SCE_in;
  logic CRC_ERR, CRC_ERR_in;
  logic TE, TE_in;
  logic SYMBOL_ERROR, SYMBOL_ERROR_in;
  logic VDSI_ERR, VDSI_ERR_in;
  logic CLK_ERR, CLK_ERR_in;
  logic[7:0] SYMBOL_COUNT, SYMBOL_COUNT_in;
  logic SCE_set, CRC_ERR_set, TE_set, SYMBOL_ERROR_set, VDSI_ERR_set, CLK_ERR_set, SYMBOL_COUNT_set;

  modport master (
    input SCE_in, CRC_ERR_in, TE_in, SYMBOL_ERROR_in, VDSI_ERR_in, CLK_ERR_in, SYMBOL_COUNT_in, SCE_set, CRC_ERR_set, TE_set, SYMBOL_ERROR_set, VDSI_ERR_set, CLK_ERR_set, SYMBOL_COUNT_set, 
    output value, SCE, CRC_ERR, TE, SYMBOL_ERROR, VDSI_ERR, CLK_ERR, SYMBOL_COUNT
  );

  modport slave (
    input value, SCE, CRC_ERR, TE, SYMBOL_ERROR, VDSI_ERR, CLK_ERR, SYMBOL_COUNT, 
    output SCE_in, CRC_ERR_in, TE_in, SYMBOL_ERROR_in, VDSI_ERR_in, CLK_ERR_in, SYMBOL_COUNT_in, SCE_set, CRC_ERR_set, TE_set, SYMBOL_ERROR_set, VDSI_ERR_set, CLK_ERR_set, SYMBOL_COUNT_set
  );

endinterface : DSI3_channel_registers_PACKET_STAT_if

// WAIT_TIME
interface DSI3_channel_registers_WAIT_TIME_if;
  logic[15:0] value;
  logic[14:0] TIME, TIME_in;
  logic TIME_set;

  modport master (
    input TIME_in, TIME_set, 
    output value, TIME
  );

  modport slave (
    input value, TIME, 
    output TIME_in, TIME_set
  );

endinterface : DSI3_channel_registers_WAIT_TIME_if

// SYNC
interface DSI3_channel_registers_SYNC_if;
  logic[15:0] value;
  logic PIN, PIN_in;
  logic[1:0] CHANNELS, CHANNELS_in;

  modport master (
    input PIN_in, CHANNELS_in, 
    output value, PIN, CHANNELS
  );

  modport slave (
    input value, PIN, CHANNELS, 
    output PIN_in, CHANNELS_in
  );

endinterface : DSI3_channel_registers_SYNC_if

// FRAME_STAT
interface DSI3_channel_registers_FRAME_STAT_if;
  logic[15:0] value;
  logic PC, PC_in;
  logic[7:0] PACKET_COUNT, PACKET_COUNT_in;
  logic PC_set;

  modport master (
    input PC_in, PACKET_COUNT_in, PC_set, 
    output value, PC, PACKET_COUNT
  );

  modport slave (
    input value, PC, PACKET_COUNT, 
    output PC_in, PACKET_COUNT_in, PC_set
  );

endinterface : DSI3_channel_registers_FRAME_STAT_if



/*###   DSI_STAT   ######################################################*/
module DSI3_channel_registers_DSI_STAT #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   input logic[addr_width-1:0] addr,
   input logic           rd,
   output logic[15:0]     data_out,
   DSI3_channel_registers_DSI_STAT_if.master DSI3_channel_registers_DSI_STAT);

   // DSI_STAT : SLAVES
   logic[3:0]  SLAVES;


   always_comb begin
       SLAVES = DSI3_channel_registers_DSI_STAT.SLAVES_in;
   end

   assign DSI3_channel_registers_DSI_STAT.SLAVES = SLAVES;

   // DSI_STAT : SYNC
   logic  SYNC;


   always_comb begin
       SYNC = DSI3_channel_registers_DSI_STAT.SYNC_in;
   end

   assign DSI3_channel_registers_DSI_STAT.SYNC = SYNC;

   // DSI_STAT : DSIUV
   logic  DSIUV;


   always_comb begin
       DSIUV = DSI3_channel_registers_DSI_STAT.DSIUV_in;
   end

   assign DSI3_channel_registers_DSI_STAT.DSIUV = DSIUV;

   // DSI_STAT : DSIOV
   logic  DSIOV;


   always_comb begin
       DSIOV = DSI3_channel_registers_DSI_STAT.DSIOV_in;
   end

   assign DSI3_channel_registers_DSI_STAT.DSIOV = DSIOV;

   // DSI_STAT : PULSECNT
   logic[7:0]  PULSECNT;


   always_comb begin
       PULSECNT = DSI3_channel_registers_DSI_STAT.PULSECNT_in;
   end

   assign DSI3_channel_registers_DSI_STAT.PULSECNT = PULSECNT;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {1'd0, SLAVES, SYNC, DSIUV, DSIOV, PULSECNT} : '0;

   assign DSI3_channel_registers_DSI_STAT.value = {1'd0, SLAVES, SYNC, DSIUV, DSIOV, PULSECNT};

endmodule : DSI3_channel_registers_DSI_STAT

/*###   PDCM_PERIOD   ######################################################*/
module DSI3_channel_registers_PDCM_PERIOD #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic           rd,
   output logic[15:0]     data_out,
   DSI3_channel_registers_PDCM_PERIOD_if.master DSI3_channel_registers_PDCM_PERIOD);

   // PDCM_PERIOD : PDCMPER
   logic[15:0]  PDCMPER, PDCMPER_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       PDCMPER <= 16'b1111101000;
     end
     else begin
       PDCMPER <= PDCMPER_nxt;
     end
   end

   always_comb begin
     PDCMPER_nxt = PDCMPER;
     if (DSI3_channel_registers_PDCM_PERIOD.PDCMPER_set == 1'b1) begin
       PDCMPER_nxt = DSI3_channel_registers_PDCM_PERIOD.PDCMPER_in;
     end
   end

   assign DSI3_channel_registers_PDCM_PERIOD.PDCMPER = PDCMPER;

   `ifdef VCS

     property PDCMPER_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (DSI3_channel_registers_PDCM_PERIOD.PDCMPER_set !== 1'bx);
     endproperty
      as_PDCMPER_set_not_x : assert property (PDCMPER_set_not_x) else $error("DSI3_channel_registers_PDCM_PERIOD.PDCMPER_set is x after reset");
     cov_PDCMPER_set_not_x :  cover property (PDCMPER_set_not_x);

   `endif

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {PDCMPER} : '0;

   assign DSI3_channel_registers_PDCM_PERIOD.value = {PDCMPER};
   assign DSI3_channel_registers_PDCM_PERIOD.access_rd = ((rd == 1'b1) && (reg_addr[addr_width-1:0] == addr )) ? 1'b1 : 1'b0;

endmodule : DSI3_channel_registers_PDCM_PERIOD

/*###   DSI_LOAD   ######################################################*/
module DSI3_channel_registers_DSI_LOAD #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   DSI3_channel_registers_DSI_LOAD_if.master DSI3_channel_registers_DSI_LOAD);

   // DSI_LOAD : START_MEASUREMENT
   logic  START_MEASUREMENT, START_MEASUREMENT_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       START_MEASUREMENT <= 1'b0;
     end
     else begin
       START_MEASUREMENT <= START_MEASUREMENT_nxt;
     end
   end

   always_comb begin
     START_MEASUREMENT_nxt = START_MEASUREMENT;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       START_MEASUREMENT_nxt = data_in[15:15]; 
     end
     if (DSI3_channel_registers_DSI_LOAD.START_MEASUREMENT_set == 1'b1) begin
       START_MEASUREMENT_nxt = DSI3_channel_registers_DSI_LOAD.START_MEASUREMENT_in;
     end
   end

   assign DSI3_channel_registers_DSI_LOAD.START_MEASUREMENT = START_MEASUREMENT;

   `ifdef VCS

     property START_MEASUREMENT_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (DSI3_channel_registers_DSI_LOAD.START_MEASUREMENT_set !== 1'bx);
     endproperty
      as_START_MEASUREMENT_set_not_x : assert property (START_MEASUREMENT_set_not_x) else $error("DSI3_channel_registers_DSI_LOAD.START_MEASUREMENT_set is x after reset");
     cov_START_MEASUREMENT_set_not_x :  cover property (START_MEASUREMENT_set_not_x);

   `endif

   // DSI_LOAD : IDLE
   logic  IDLE, IDLE_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       IDLE <= 1'b1;
     end
     else begin
       IDLE <= IDLE_nxt;
     end
   end

   always_comb begin
     IDLE_nxt = IDLE;
     if (DSI3_channel_registers_DSI_LOAD.IDLE_set == 1'b1) begin
       IDLE_nxt = DSI3_channel_registers_DSI_LOAD.IDLE_in;
     end
   end

   assign DSI3_channel_registers_DSI_LOAD.IDLE = IDLE;

   `ifdef VCS

     property IDLE_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (DSI3_channel_registers_DSI_LOAD.IDLE_set !== 1'bx);
     endproperty
      as_IDLE_set_not_x : assert property (IDLE_set_not_x) else $error("DSI3_channel_registers_DSI_LOAD.IDLE_set is x after reset");
     cov_IDLE_set_not_x :  cover property (IDLE_set_not_x);

   `endif

   // DSI_LOAD : LOAD
   logic[4:0]  LOAD, LOAD_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       LOAD <= 5'b0;
     end
     else begin
       LOAD <= LOAD_nxt;
     end
   end

   always_comb begin
     LOAD_nxt = LOAD;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       LOAD_nxt = data_in[4:0]; 
     end
     if (DSI3_channel_registers_DSI_LOAD.LOAD_set == 1'b1) begin
       LOAD_nxt = DSI3_channel_registers_DSI_LOAD.LOAD_in;
     end
   end

   assign DSI3_channel_registers_DSI_LOAD.LOAD = LOAD;

   `ifdef VCS

     property LOAD_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (DSI3_channel_registers_DSI_LOAD.LOAD_set !== 1'bx);
     endproperty
      as_LOAD_set_not_x : assert property (LOAD_set_not_x) else $error("DSI3_channel_registers_DSI_LOAD.LOAD_set is x after reset");
     cov_LOAD_set_not_x :  cover property (LOAD_set_not_x);

   `endif

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {START_MEASUREMENT, IDLE, 9'd0, LOAD} : '0;

   assign DSI3_channel_registers_DSI_LOAD.value = {START_MEASUREMENT, IDLE, 9'd0, LOAD};

endmodule : DSI3_channel_registers_DSI_LOAD

/*###   DSI_IRQ_STAT   ######################################################*/
module DSI3_channel_registers_DSI_IRQ_STAT #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   DSI3_channel_registers_DSI_IRQ_STAT_if.master DSI3_channel_registers_DSI_IRQ_STAT);

   // DSI_IRQ_STAT : IQ_ERR
   logic  IQ_ERR, IQ_ERR_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       IQ_ERR <= 1'b0;
     end
     else begin
       IQ_ERR <= IQ_ERR_nxt;
     end
   end

   always_comb begin
     IQ_ERR_nxt = IQ_ERR;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[6])) begin
       IQ_ERR_nxt = IQ_ERR & (~data_in[6]);
     end
     if (DSI3_channel_registers_DSI_IRQ_STAT.IQ_ERR_set == 1'b1) begin
       IQ_ERR_nxt = DSI3_channel_registers_DSI_IRQ_STAT.IQ_ERR_in;
     end
   end

   assign DSI3_channel_registers_DSI_IRQ_STAT.IQ_ERR = IQ_ERR;

   `ifdef VCS

     property IQ_ERR_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (DSI3_channel_registers_DSI_IRQ_STAT.IQ_ERR_set !== 1'bx);
     endproperty
      as_IQ_ERR_set_not_x : assert property (IQ_ERR_set_not_x) else $error("DSI3_channel_registers_DSI_IRQ_STAT.IQ_ERR_set is x after reset");
     cov_IQ_ERR_set_not_x :  cover property (IQ_ERR_set_not_x);

   `endif

   // DSI_IRQ_STAT : COM_ERR
   logic  COM_ERR, COM_ERR_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       COM_ERR <= 1'b0;
     end
     else begin
       COM_ERR <= COM_ERR_nxt;
     end
   end

   always_comb begin
     COM_ERR_nxt = COM_ERR;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[5])) begin
       COM_ERR_nxt = COM_ERR & (~data_in[5]);
     end
     if (DSI3_channel_registers_DSI_IRQ_STAT.COM_ERR_set == 1'b1) begin
       COM_ERR_nxt = DSI3_channel_registers_DSI_IRQ_STAT.COM_ERR_in;
     end
   end

   assign DSI3_channel_registers_DSI_IRQ_STAT.COM_ERR = COM_ERR;

   `ifdef VCS

     property COM_ERR_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (DSI3_channel_registers_DSI_IRQ_STAT.COM_ERR_set !== 1'bx);
     endproperty
      as_COM_ERR_set_not_x : assert property (COM_ERR_set_not_x) else $error("DSI3_channel_registers_DSI_IRQ_STAT.COM_ERR_set is x after reset");
     cov_COM_ERR_set_not_x :  cover property (COM_ERR_set_not_x);

   `endif

   // DSI_IRQ_STAT : DMOF
   logic  DMOF, DMOF_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DMOF <= 1'b0;
     end
     else begin
       DMOF <= DMOF_nxt;
     end
   end

   always_comb begin
     DMOF_nxt = DMOF;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[4])) begin
       DMOF_nxt = DMOF & (~data_in[4]);
     end
     if (DSI3_channel_registers_DSI_IRQ_STAT.DMOF_set == 1'b1) begin
       DMOF_nxt = DSI3_channel_registers_DSI_IRQ_STAT.DMOF_in;
     end
   end

   assign DSI3_channel_registers_DSI_IRQ_STAT.DMOF = DMOF;

   `ifdef VCS

     property DMOF_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (DSI3_channel_registers_DSI_IRQ_STAT.DMOF_set !== 1'bx);
     endproperty
      as_DMOF_set_not_x : assert property (DMOF_set_not_x) else $error("DSI3_channel_registers_DSI_IRQ_STAT.DMOF_set is x after reset");
     cov_DMOF_set_not_x :  cover property (DMOF_set_not_x);

   `endif

   // DSI_IRQ_STAT : HW_FAIL
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
     if (DSI3_channel_registers_DSI_IRQ_STAT.HW_FAIL_set == 1'b1) begin
       HW_FAIL_nxt = DSI3_channel_registers_DSI_IRQ_STAT.HW_FAIL_in;
     end
   end

   assign DSI3_channel_registers_DSI_IRQ_STAT.HW_FAIL = HW_FAIL;

   `ifdef VCS

     property HW_FAIL_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (DSI3_channel_registers_DSI_IRQ_STAT.HW_FAIL_set !== 1'bx);
     endproperty
      as_HW_FAIL_set_not_x : assert property (HW_FAIL_set_not_x) else $error("DSI3_channel_registers_DSI_IRQ_STAT.HW_FAIL_set is x after reset");
     cov_HW_FAIL_set_not_x :  cover property (HW_FAIL_set_not_x);

   `endif

   // DSI_IRQ_STAT : SYNC_ERR
   logic  SYNC_ERR, SYNC_ERR_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       SYNC_ERR <= 1'b0;
     end
     else begin
       SYNC_ERR <= SYNC_ERR_nxt;
     end
   end

   always_comb begin
     SYNC_ERR_nxt = SYNC_ERR;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[2])) begin
       SYNC_ERR_nxt = SYNC_ERR & (~data_in[2]);
     end
     if (DSI3_channel_registers_DSI_IRQ_STAT.SYNC_ERR_set == 1'b1) begin
       SYNC_ERR_nxt = DSI3_channel_registers_DSI_IRQ_STAT.SYNC_ERR_in;
     end
   end

   assign DSI3_channel_registers_DSI_IRQ_STAT.SYNC_ERR = SYNC_ERR;

   `ifdef VCS

     property SYNC_ERR_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (DSI3_channel_registers_DSI_IRQ_STAT.SYNC_ERR_set !== 1'bx);
     endproperty
      as_SYNC_ERR_set_not_x : assert property (SYNC_ERR_set_not_x) else $error("DSI3_channel_registers_DSI_IRQ_STAT.SYNC_ERR_set is x after reset");
     cov_SYNC_ERR_set_not_x :  cover property (SYNC_ERR_set_not_x);

   `endif

   // DSI_IRQ_STAT : DSIUV
   logic  DSIUV, DSIUV_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DSIUV <= 1'b0;
     end
     else begin
       DSIUV <= DSIUV_nxt;
     end
   end

   always_comb begin
     DSIUV_nxt = DSIUV;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[1])) begin
       DSIUV_nxt = DSIUV & (~data_in[1]);
     end
     if (DSI3_channel_registers_DSI_IRQ_STAT.DSIUV_set == 1'b1) begin
       DSIUV_nxt = DSI3_channel_registers_DSI_IRQ_STAT.DSIUV_in;
     end
   end

   assign DSI3_channel_registers_DSI_IRQ_STAT.DSIUV = DSIUV;

   `ifdef VCS

     property DSIUV_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (DSI3_channel_registers_DSI_IRQ_STAT.DSIUV_set !== 1'bx);
     endproperty
      as_DSIUV_set_not_x : assert property (DSIUV_set_not_x) else $error("DSI3_channel_registers_DSI_IRQ_STAT.DSIUV_set is x after reset");
     cov_DSIUV_set_not_x :  cover property (DSIUV_set_not_x);

   `endif

   // DSI_IRQ_STAT : DSIOV
   logic  DSIOV, DSIOV_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DSIOV <= 1'b0;
     end
     else begin
       DSIOV <= DSIOV_nxt;
     end
   end

   always_comb begin
     DSIOV_nxt = DSIOV;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr) && |(data_in[0])) begin
       DSIOV_nxt = DSIOV & (~data_in[0]);
     end
     if (DSI3_channel_registers_DSI_IRQ_STAT.DSIOV_set == 1'b1) begin
       DSIOV_nxt = DSI3_channel_registers_DSI_IRQ_STAT.DSIOV_in;
     end
   end

   assign DSI3_channel_registers_DSI_IRQ_STAT.DSIOV = DSIOV;

   `ifdef VCS

     property DSIOV_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (DSI3_channel_registers_DSI_IRQ_STAT.DSIOV_set !== 1'bx);
     endproperty
      as_DSIOV_set_not_x : assert property (DSIOV_set_not_x) else $error("DSI3_channel_registers_DSI_IRQ_STAT.DSIOV_set is x after reset");
     cov_DSIOV_set_not_x :  cover property (DSIOV_set_not_x);

   `endif

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {9'd0, IQ_ERR, COM_ERR, DMOF, HW_FAIL, SYNC_ERR, DSIUV, DSIOV} : '0;

   assign DSI3_channel_registers_DSI_IRQ_STAT.value = {9'd0, IQ_ERR, COM_ERR, DMOF, HW_FAIL, SYNC_ERR, DSIUV, DSIOV};

endmodule : DSI3_channel_registers_DSI_IRQ_STAT

/*###   DSI_IRQ_MASK   ######################################################*/
module DSI3_channel_registers_DSI_IRQ_MASK #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   DSI3_channel_registers_DSI_IRQ_MASK_if.master DSI3_channel_registers_DSI_IRQ_MASK);

   // DSI_IRQ_MASK : IQ_ERR
   logic  IQ_ERR, IQ_ERR_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       IQ_ERR <= 1'b1;
     end
     else begin
       IQ_ERR <= IQ_ERR_nxt;
     end
   end

   always_comb begin
     IQ_ERR_nxt = IQ_ERR;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       IQ_ERR_nxt = data_in[6:6]; 
     end
   end

   assign DSI3_channel_registers_DSI_IRQ_MASK.IQ_ERR = IQ_ERR;

   // DSI_IRQ_MASK : COM_ERR
   logic  COM_ERR, COM_ERR_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       COM_ERR <= 1'b1;
     end
     else begin
       COM_ERR <= COM_ERR_nxt;
     end
   end

   always_comb begin
     COM_ERR_nxt = COM_ERR;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       COM_ERR_nxt = data_in[5:5]; 
     end
   end

   assign DSI3_channel_registers_DSI_IRQ_MASK.COM_ERR = COM_ERR;

   // DSI_IRQ_MASK : DMOF
   logic  DMOF, DMOF_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DMOF <= 1'b1;
     end
     else begin
       DMOF <= DMOF_nxt;
     end
   end

   always_comb begin
     DMOF_nxt = DMOF;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       DMOF_nxt = data_in[4:4]; 
     end
   end

   assign DSI3_channel_registers_DSI_IRQ_MASK.DMOF = DMOF;

   // DSI_IRQ_MASK : HW_FAIL
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

   assign DSI3_channel_registers_DSI_IRQ_MASK.HW_FAIL = HW_FAIL;

   // DSI_IRQ_MASK : SYNC_ERR
   logic  SYNC_ERR, SYNC_ERR_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       SYNC_ERR <= 1'b1;
     end
     else begin
       SYNC_ERR <= SYNC_ERR_nxt;
     end
   end

   always_comb begin
     SYNC_ERR_nxt = SYNC_ERR;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       SYNC_ERR_nxt = data_in[2:2]; 
     end
   end

   assign DSI3_channel_registers_DSI_IRQ_MASK.SYNC_ERR = SYNC_ERR;

   // DSI_IRQ_MASK : DSIUV
   logic  DSIUV, DSIUV_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DSIUV <= 1'b1;
     end
     else begin
       DSIUV <= DSIUV_nxt;
     end
   end

   always_comb begin
     DSIUV_nxt = DSIUV;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       DSIUV_nxt = data_in[1:1]; 
     end
   end

   assign DSI3_channel_registers_DSI_IRQ_MASK.DSIUV = DSIUV;

   // DSI_IRQ_MASK : DSIOV
   logic  DSIOV, DSIOV_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       DSIOV <= 1'b1;
     end
     else begin
       DSIOV <= DSIOV_nxt;
     end
   end

   always_comb begin
     DSIOV_nxt = DSIOV;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       DSIOV_nxt = data_in[0:0]; 
     end
   end

   assign DSI3_channel_registers_DSI_IRQ_MASK.DSIOV = DSIOV;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {9'd0, IQ_ERR, COM_ERR, DMOF, HW_FAIL, SYNC_ERR, DSIUV, DSIOV} : '0;

   assign DSI3_channel_registers_DSI_IRQ_MASK.value = {9'd0, IQ_ERR, COM_ERR, DMOF, HW_FAIL, SYNC_ERR, DSIUV, DSIOV};

endmodule : DSI3_channel_registers_DSI_IRQ_MASK

/*###   DSI_CMD   ######################################################*/
module DSI3_channel_registers_DSI_CMD #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   input logic[addr_width-1:0] addr,
   input logic           rd,
   output logic[15:0]     data_out,
   DSI3_channel_registers_DSI_CMD_if.master DSI3_channel_registers_DSI_CMD);

   // DSI_CMD : CMD
   logic[3:0]  CMD;


   always_comb begin
       CMD = DSI3_channel_registers_DSI_CMD.CMD_in;
   end

   assign DSI3_channel_registers_DSI_CMD.CMD = CMD;

   // DSI_CMD : DATA
   logic[11:0]  DATA;


   always_comb begin
       DATA = DSI3_channel_registers_DSI_CMD.DATA_in;
   end

   assign DSI3_channel_registers_DSI_CMD.DATA = DATA;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {CMD, DATA} : '0;

   assign DSI3_channel_registers_DSI_CMD.value = {CMD, DATA};

endmodule : DSI3_channel_registers_DSI_CMD

/*###   CRM_WORD2   ######################################################*/
module DSI3_channel_registers_CRM_WORD2 #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   input logic[addr_width-1:0] addr,
   input logic           rd,
   output logic[15:0]     data_out,
   DSI3_channel_registers_CRM_WORD2_if.master DSI3_channel_registers_CRM_WORD2);

   // CRM_WORD2 : CRM_WORD2
   logic[15:0]  CRM_WORD2;


   always_comb begin
       CRM_WORD2 = DSI3_channel_registers_CRM_WORD2.CRM_WORD2_in;
   end

   assign DSI3_channel_registers_CRM_WORD2.CRM_WORD2 = CRM_WORD2;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {CRM_WORD2} : '0;

   assign DSI3_channel_registers_CRM_WORD2.value = {CRM_WORD2};

endmodule : DSI3_channel_registers_CRM_WORD2

/*###   CRM_WORD1   ######################################################*/
module DSI3_channel_registers_CRM_WORD1 #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   input logic[addr_width-1:0] addr,
   input logic           rd,
   output logic[15:0]     data_out,
   DSI3_channel_registers_CRM_WORD1_if.master DSI3_channel_registers_CRM_WORD1);

   // CRM_WORD1 : CRM_WORD1
   logic[15:0]  CRM_WORD1;


   always_comb begin
       CRM_WORD1 = DSI3_channel_registers_CRM_WORD1.CRM_WORD1_in;
   end

   assign DSI3_channel_registers_CRM_WORD1.CRM_WORD1 = CRM_WORD1;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {CRM_WORD1} : '0;

   assign DSI3_channel_registers_CRM_WORD1.value = {CRM_WORD1};

endmodule : DSI3_channel_registers_CRM_WORD1

/*###   PACKET_STAT   ######################################################*/
module DSI3_channel_registers_PACKET_STAT #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic           rd,
   output logic[15:0]     data_out,
   DSI3_channel_registers_PACKET_STAT_if.master DSI3_channel_registers_PACKET_STAT);

   // PACKET_STAT : SCE
   logic  SCE, SCE_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       SCE <= 1'b0;
     end
     else begin
       SCE <= SCE_nxt;
     end
   end

   always_comb begin
     SCE_nxt = SCE;
     if (DSI3_channel_registers_PACKET_STAT.SCE_set == 1'b1) begin
       SCE_nxt = DSI3_channel_registers_PACKET_STAT.SCE_in;
     end
   end

   assign DSI3_channel_registers_PACKET_STAT.SCE = SCE;

   `ifdef VCS

     property SCE_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (DSI3_channel_registers_PACKET_STAT.SCE_set !== 1'bx);
     endproperty
      as_SCE_set_not_x : assert property (SCE_set_not_x) else $error("DSI3_channel_registers_PACKET_STAT.SCE_set is x after reset");
     cov_SCE_set_not_x :  cover property (SCE_set_not_x);

   `endif

   // PACKET_STAT : CRC_ERR
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
     if (DSI3_channel_registers_PACKET_STAT.CRC_ERR_set == 1'b1) begin
       CRC_ERR_nxt = DSI3_channel_registers_PACKET_STAT.CRC_ERR_in;
     end
   end

   assign DSI3_channel_registers_PACKET_STAT.CRC_ERR = CRC_ERR;

   `ifdef VCS

     property CRC_ERR_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (DSI3_channel_registers_PACKET_STAT.CRC_ERR_set !== 1'bx);
     endproperty
      as_CRC_ERR_set_not_x : assert property (CRC_ERR_set_not_x) else $error("DSI3_channel_registers_PACKET_STAT.CRC_ERR_set is x after reset");
     cov_CRC_ERR_set_not_x :  cover property (CRC_ERR_set_not_x);

   `endif

   // PACKET_STAT : TE
   logic  TE, TE_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       TE <= 1'b0;
     end
     else begin
       TE <= TE_nxt;
     end
   end

   always_comb begin
     TE_nxt = TE;
     if (DSI3_channel_registers_PACKET_STAT.TE_set == 1'b1) begin
       TE_nxt = DSI3_channel_registers_PACKET_STAT.TE_in;
     end
   end

   assign DSI3_channel_registers_PACKET_STAT.TE = TE;

   `ifdef VCS

     property TE_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (DSI3_channel_registers_PACKET_STAT.TE_set !== 1'bx);
     endproperty
      as_TE_set_not_x : assert property (TE_set_not_x) else $error("DSI3_channel_registers_PACKET_STAT.TE_set is x after reset");
     cov_TE_set_not_x :  cover property (TE_set_not_x);

   `endif

   // PACKET_STAT : SYMBOL_ERROR
   logic  SYMBOL_ERROR, SYMBOL_ERROR_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       SYMBOL_ERROR <= 1'b0;
     end
     else begin
       SYMBOL_ERROR <= SYMBOL_ERROR_nxt;
     end
   end

   always_comb begin
     SYMBOL_ERROR_nxt = SYMBOL_ERROR;
     if (DSI3_channel_registers_PACKET_STAT.SYMBOL_ERROR_set == 1'b1) begin
       SYMBOL_ERROR_nxt = DSI3_channel_registers_PACKET_STAT.SYMBOL_ERROR_in;
     end
   end

   assign DSI3_channel_registers_PACKET_STAT.SYMBOL_ERROR = SYMBOL_ERROR;

   `ifdef VCS

     property SYMBOL_ERROR_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (DSI3_channel_registers_PACKET_STAT.SYMBOL_ERROR_set !== 1'bx);
     endproperty
      as_SYMBOL_ERROR_set_not_x : assert property (SYMBOL_ERROR_set_not_x) else $error("DSI3_channel_registers_PACKET_STAT.SYMBOL_ERROR_set is x after reset");
     cov_SYMBOL_ERROR_set_not_x :  cover property (SYMBOL_ERROR_set_not_x);

   `endif

   // PACKET_STAT : VDSI_ERR
   logic  VDSI_ERR, VDSI_ERR_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       VDSI_ERR <= 1'b0;
     end
     else begin
       VDSI_ERR <= VDSI_ERR_nxt;
     end
   end

   always_comb begin
     VDSI_ERR_nxt = VDSI_ERR;
     if (DSI3_channel_registers_PACKET_STAT.VDSI_ERR_set == 1'b1) begin
       VDSI_ERR_nxt = DSI3_channel_registers_PACKET_STAT.VDSI_ERR_in;
     end
   end

   assign DSI3_channel_registers_PACKET_STAT.VDSI_ERR = VDSI_ERR;

   `ifdef VCS

     property VDSI_ERR_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (DSI3_channel_registers_PACKET_STAT.VDSI_ERR_set !== 1'bx);
     endproperty
      as_VDSI_ERR_set_not_x : assert property (VDSI_ERR_set_not_x) else $error("DSI3_channel_registers_PACKET_STAT.VDSI_ERR_set is x after reset");
     cov_VDSI_ERR_set_not_x :  cover property (VDSI_ERR_set_not_x);

   `endif

   // PACKET_STAT : CLK_ERR
   logic  CLK_ERR, CLK_ERR_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       CLK_ERR <= 1'b0;
     end
     else begin
       CLK_ERR <= CLK_ERR_nxt;
     end
   end

   always_comb begin
     CLK_ERR_nxt = CLK_ERR;
     if (DSI3_channel_registers_PACKET_STAT.CLK_ERR_set == 1'b1) begin
       CLK_ERR_nxt = DSI3_channel_registers_PACKET_STAT.CLK_ERR_in;
     end
   end

   assign DSI3_channel_registers_PACKET_STAT.CLK_ERR = CLK_ERR;

   `ifdef VCS

     property CLK_ERR_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (DSI3_channel_registers_PACKET_STAT.CLK_ERR_set !== 1'bx);
     endproperty
      as_CLK_ERR_set_not_x : assert property (CLK_ERR_set_not_x) else $error("DSI3_channel_registers_PACKET_STAT.CLK_ERR_set is x after reset");
     cov_CLK_ERR_set_not_x :  cover property (CLK_ERR_set_not_x);

   `endif

   // PACKET_STAT : SYMBOL_COUNT
   logic[7:0]  SYMBOL_COUNT, SYMBOL_COUNT_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       SYMBOL_COUNT <= 8'b0;
     end
     else begin
       SYMBOL_COUNT <= SYMBOL_COUNT_nxt;
     end
   end

   always_comb begin
     SYMBOL_COUNT_nxt = SYMBOL_COUNT;
     if (DSI3_channel_registers_PACKET_STAT.SYMBOL_COUNT_set == 1'b1) begin
       SYMBOL_COUNT_nxt = DSI3_channel_registers_PACKET_STAT.SYMBOL_COUNT_in;
     end
   end

   assign DSI3_channel_registers_PACKET_STAT.SYMBOL_COUNT = SYMBOL_COUNT;

   `ifdef VCS

     property SYMBOL_COUNT_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (DSI3_channel_registers_PACKET_STAT.SYMBOL_COUNT_set !== 1'bx);
     endproperty
      as_SYMBOL_COUNT_set_not_x : assert property (SYMBOL_COUNT_set_not_x) else $error("DSI3_channel_registers_PACKET_STAT.SYMBOL_COUNT_set is x after reset");
     cov_SYMBOL_COUNT_set_not_x :  cover property (SYMBOL_COUNT_set_not_x);

   `endif

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {2'd0, SCE, CRC_ERR, TE, SYMBOL_ERROR, VDSI_ERR, CLK_ERR, SYMBOL_COUNT} : '0;

   assign DSI3_channel_registers_PACKET_STAT.value = {2'd0, SCE, CRC_ERR, TE, SYMBOL_ERROR, VDSI_ERR, CLK_ERR, SYMBOL_COUNT};

endmodule : DSI3_channel_registers_PACKET_STAT

/*###   WAIT_TIME   ######################################################*/
module DSI3_channel_registers_WAIT_TIME #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic           rd,
   output logic[15:0]     data_out,
   DSI3_channel_registers_WAIT_TIME_if.master DSI3_channel_registers_WAIT_TIME);

   // WAIT_TIME : TIME
   logic[14:0]  TIME, TIME_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       TIME <= 15'b0;
     end
     else begin
       TIME <= TIME_nxt;
     end
   end

   always_comb begin
     TIME_nxt = TIME;
     if (DSI3_channel_registers_WAIT_TIME.TIME_set == 1'b1) begin
       TIME_nxt = DSI3_channel_registers_WAIT_TIME.TIME_in;
     end
   end

   assign DSI3_channel_registers_WAIT_TIME.TIME = TIME;

   `ifdef VCS

     property TIME_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (DSI3_channel_registers_WAIT_TIME.TIME_set !== 1'bx);
     endproperty
      as_TIME_set_not_x : assert property (TIME_set_not_x) else $error("DSI3_channel_registers_WAIT_TIME.TIME_set is x after reset");
     cov_TIME_set_not_x :  cover property (TIME_set_not_x);

   `endif

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {1'd0, TIME} : '0;

   assign DSI3_channel_registers_WAIT_TIME.value = {1'd0, TIME};

endmodule : DSI3_channel_registers_WAIT_TIME

/*###   SYNC   ######################################################*/
module DSI3_channel_registers_SYNC #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   input logic[addr_width-1:0] addr,
   input logic           rd,
   output logic[15:0]     data_out,
   DSI3_channel_registers_SYNC_if.master DSI3_channel_registers_SYNC);

   // SYNC : PIN
   logic  PIN;


   always_comb begin
       PIN = DSI3_channel_registers_SYNC.PIN_in;
   end

   assign DSI3_channel_registers_SYNC.PIN = PIN;

   // SYNC : CHANNELS
   logic[1:0]  CHANNELS;


   always_comb begin
       CHANNELS = DSI3_channel_registers_SYNC.CHANNELS_in;
   end

   assign DSI3_channel_registers_SYNC.CHANNELS = CHANNELS;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {11'd0, PIN, 2'd0, CHANNELS} : '0;

   assign DSI3_channel_registers_SYNC.value = {11'd0, PIN, 2'd0, CHANNELS};

endmodule : DSI3_channel_registers_SYNC

/*###   FRAME_STAT   ######################################################*/
module DSI3_channel_registers_FRAME_STAT #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic           rd,
   output logic[15:0]     data_out,
   DSI3_channel_registers_FRAME_STAT_if.master DSI3_channel_registers_FRAME_STAT);

   // FRAME_STAT : PC
   logic  PC, PC_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       PC <= 1'b0;
     end
     else begin
       PC <= PC_nxt;
     end
   end

   always_comb begin
     PC_nxt = PC;
     if (DSI3_channel_registers_FRAME_STAT.PC_set == 1'b1) begin
       PC_nxt = DSI3_channel_registers_FRAME_STAT.PC_in;
     end
   end

   assign DSI3_channel_registers_FRAME_STAT.PC = PC;

   `ifdef VCS

     property PC_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (DSI3_channel_registers_FRAME_STAT.PC_set !== 1'bx);
     endproperty
      as_PC_set_not_x : assert property (PC_set_not_x) else $error("DSI3_channel_registers_FRAME_STAT.PC_set is x after reset");
     cov_PC_set_not_x :  cover property (PC_set_not_x);

   `endif

   // FRAME_STAT : PACKET_COUNT
   logic[7:0]  PACKET_COUNT;


   always_comb begin
       PACKET_COUNT = DSI3_channel_registers_FRAME_STAT.PACKET_COUNT_in;
   end

   assign DSI3_channel_registers_FRAME_STAT.PACKET_COUNT = PACKET_COUNT;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {PC, 7'd0, PACKET_COUNT} : '0;

   assign DSI3_channel_registers_FRAME_STAT.value = {PC, 7'd0, PACKET_COUNT};

endmodule : DSI3_channel_registers_FRAME_STAT

/*###   Registers   ######################################################*/
module DSI3_channel_registers #(
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
   DSI3_channel_registers_DSI_STAT_if.master DSI3_channel_registers_DSI_STAT,
   DSI3_channel_registers_PDCM_PERIOD_if.master DSI3_channel_registers_PDCM_PERIOD,
   DSI3_channel_registers_DSI_LOAD_if.master DSI3_channel_registers_DSI_LOAD,
   DSI3_channel_registers_DSI_IRQ_STAT_if.master DSI3_channel_registers_DSI_IRQ_STAT,
   DSI3_channel_registers_DSI_IRQ_MASK_if.master DSI3_channel_registers_DSI_IRQ_MASK,
   DSI3_channel_registers_DSI_CMD_if.master DSI3_channel_registers_DSI_CMD,
   DSI3_channel_registers_CRM_WORD2_if.master DSI3_channel_registers_CRM_WORD2,
   DSI3_channel_registers_CRM_WORD1_if.master DSI3_channel_registers_CRM_WORD1,
   DSI3_channel_registers_PACKET_STAT_if.master DSI3_channel_registers_PACKET_STAT,
   DSI3_channel_registers_WAIT_TIME_if.master DSI3_channel_registers_WAIT_TIME,
   DSI3_channel_registers_SYNC_if.master DSI3_channel_registers_SYNC,
   DSI3_channel_registers_FRAME_STAT_if.master DSI3_channel_registers_FRAME_STAT
);

   logic[15:0] data_out_DSI_STAT, data_out_PDCM_PERIOD, data_out_DSI_LOAD, data_out_DSI_IRQ_STAT, data_out_DSI_IRQ_MASK, data_out_DSI_CMD, data_out_CRM_WORD2, data_out_CRM_WORD1, data_out_PACKET_STAT, data_out_WAIT_TIME, data_out_SYNC, data_out_FRAME_STAT;

   DSI3_channel_registers_DSI_STAT #( .reg_addr (base_addr + 'h0), .addr_width(addr_width) ) i_DSI3_channel_registers_DSI_STAT ( .data_out (data_out_DSI_STAT), .*);
   DSI3_channel_registers_PDCM_PERIOD #( .reg_addr (base_addr + 'h4), .addr_width(addr_width) ) i_DSI3_channel_registers_PDCM_PERIOD ( .data_out (data_out_PDCM_PERIOD), .*);
   DSI3_channel_registers_DSI_LOAD #( .reg_addr (base_addr + 'h5), .addr_width(addr_width) ) i_DSI3_channel_registers_DSI_LOAD ( .data_out (data_out_DSI_LOAD), .*);
   DSI3_channel_registers_DSI_IRQ_STAT #( .reg_addr (base_addr + 'h8), .addr_width(addr_width) ) i_DSI3_channel_registers_DSI_IRQ_STAT ( .data_out (data_out_DSI_IRQ_STAT), .*);
   DSI3_channel_registers_DSI_IRQ_MASK #( .reg_addr (base_addr + 'h9), .addr_width(addr_width) ) i_DSI3_channel_registers_DSI_IRQ_MASK ( .data_out (data_out_DSI_IRQ_MASK), .*);
   DSI3_channel_registers_DSI_CMD #( .reg_addr (base_addr + 'h10), .addr_width(addr_width) ) i_DSI3_channel_registers_DSI_CMD ( .data_out (data_out_DSI_CMD), .*);
   DSI3_channel_registers_CRM_WORD2 #( .reg_addr (base_addr + 'h11), .addr_width(addr_width) ) i_DSI3_channel_registers_CRM_WORD2 ( .data_out (data_out_CRM_WORD2), .*);
   DSI3_channel_registers_CRM_WORD1 #( .reg_addr (base_addr + 'h12), .addr_width(addr_width) ) i_DSI3_channel_registers_CRM_WORD1 ( .data_out (data_out_CRM_WORD1), .*);
   DSI3_channel_registers_PACKET_STAT #( .reg_addr (base_addr + 'h18), .addr_width(addr_width) ) i_DSI3_channel_registers_PACKET_STAT ( .data_out (data_out_PACKET_STAT), .*);
   DSI3_channel_registers_WAIT_TIME #( .reg_addr (base_addr + 'h19), .addr_width(addr_width) ) i_DSI3_channel_registers_WAIT_TIME ( .data_out (data_out_WAIT_TIME), .*);
   DSI3_channel_registers_SYNC #( .reg_addr (base_addr + 'h1a), .addr_width(addr_width) ) i_DSI3_channel_registers_SYNC ( .data_out (data_out_SYNC), .*);
   DSI3_channel_registers_FRAME_STAT #( .reg_addr (base_addr + 'h1b), .addr_width(addr_width) ) i_DSI3_channel_registers_FRAME_STAT ( .data_out (data_out_FRAME_STAT), .*);

   // output data assignment
   assign data_out = data_out_DSI_STAT | data_out_PDCM_PERIOD | data_out_DSI_LOAD | data_out_DSI_IRQ_STAT | data_out_DSI_IRQ_MASK | data_out_DSI_CMD | data_out_CRM_WORD2 | data_out_CRM_WORD1 | data_out_PACKET_STAT | data_out_WAIT_TIME | data_out_SYNC | data_out_FRAME_STAT;

endmodule : DSI3_channel_registers
