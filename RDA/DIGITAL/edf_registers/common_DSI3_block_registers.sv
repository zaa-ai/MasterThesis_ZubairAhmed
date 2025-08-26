/* ###   interfaces   ###################################################### */

// DSI_ENABLE
interface common_DSI3_block_registers_DSI_ENABLE_if;
  logic[15:0] value;
  logic access_wr;
  logic access_rd;
  logic[1:0] TRE, TRE_in;
  logic TRE_set;

  modport master (
    input TRE_in, TRE_set, 
    output value, access_wr, access_rd, TRE
  );

  modport slave (
    input value, access_wr, access_rd, TRE, 
    output TRE_in, TRE_set
  );

endinterface : common_DSI3_block_registers_DSI_ENABLE_if

// DSI_CFG
interface common_DSI3_block_registers_DSI_CFG_if;
  logic[15:0] value;
  logic SYNC_MASTER;
  logic SYNC_PDCM;
  logic CRC_EN;
  logic[1:0] BITTIME;
  logic[1:0] CHIPTIME;

  modport master (
    output value, SYNC_MASTER, SYNC_PDCM, CRC_EN, BITTIME, CHIPTIME
  );

  modport slave (
    input value, SYNC_MASTER, SYNC_PDCM, CRC_EN, BITTIME, CHIPTIME
  );

endinterface : common_DSI3_block_registers_DSI_CFG_if

// DSI_TX_SHIFT
interface common_DSI3_block_registers_DSI_TX_SHIFT_if;
  logic[15:0] value;
  logic[6:0] SHIFT;

  modport master (
    output value, SHIFT
  );

  modport slave (
    input value, SHIFT
  );

endinterface : common_DSI3_block_registers_DSI_TX_SHIFT_if

// SYNC_IDLE_REG
interface common_DSI3_block_registers_SYNC_IDLE_REG_if;
  logic[15:0] value;
  logic PIN, PIN_in;
  logic[1:0] DSI, DSI_in;

  modport master (
    input PIN_in, DSI_in, 
    output value, PIN, DSI
  );

  modport slave (
    input value, PIN, DSI, 
    output PIN_in, DSI_in
  );

endinterface : common_DSI3_block_registers_SYNC_IDLE_REG_if

// CRM_TIME
interface common_DSI3_block_registers_CRM_TIME_if;
  logic[15:0] value;
  logic[10:0] TIME;

  modport master (
    output value, TIME
  );

  modport slave (
    input value, TIME
  );

endinterface : common_DSI3_block_registers_CRM_TIME_if

// CRM_TIME_NR
interface common_DSI3_block_registers_CRM_TIME_NR_if;
  logic[15:0] value;
  logic[10:0] TIME;

  modport master (
    output value, TIME
  );

  modport slave (
    input value, TIME
  );

endinterface : common_DSI3_block_registers_CRM_TIME_NR_if



/*###   DSI_ENABLE   ######################################################*/
module common_DSI3_block_registers_DSI_ENABLE #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   common_DSI3_block_registers_DSI_ENABLE_if.master common_DSI3_block_registers_DSI_ENABLE);

   // DSI_ENABLE : TRE
   logic[1:0]  TRE, TRE_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       TRE <= 2'b11;
     end
     else begin
       TRE <= TRE_nxt;
     end
   end

   always_comb begin
     TRE_nxt = TRE;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       TRE_nxt = data_in[1:0]; 
     end
     if (common_DSI3_block_registers_DSI_ENABLE.TRE_set == 1'b1) begin
       TRE_nxt = common_DSI3_block_registers_DSI_ENABLE.TRE_in;
     end
   end

   assign common_DSI3_block_registers_DSI_ENABLE.TRE = TRE;

   `ifdef VCS

     property TRE_set_not_x;
       disable iff($isunknown(clk_rst.rstn))
       @(posedge clk_rst.rstn) (common_DSI3_block_registers_DSI_ENABLE.TRE_set !== 1'bx);
     endproperty
      as_TRE_set_not_x : assert property (TRE_set_not_x) else $error("common_DSI3_block_registers_DSI_ENABLE.TRE_set is x after reset");
     cov_TRE_set_not_x :  cover property (TRE_set_not_x);

   `endif

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {14'd0, TRE} : '0;

   assign common_DSI3_block_registers_DSI_ENABLE.value = {14'd0, TRE};
   assign common_DSI3_block_registers_DSI_ENABLE.access_rd = ((rd == 1'b1) && (reg_addr[addr_width-1:0] == addr )) ? 1'b1 : 1'b0;
   assign common_DSI3_block_registers_DSI_ENABLE.access_wr = ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) ? 1'b1 : 1'b0;

endmodule : common_DSI3_block_registers_DSI_ENABLE

/*###   DSI_CFG   ######################################################*/
module common_DSI3_block_registers_DSI_CFG #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   common_DSI3_block_registers_DSI_CFG_if.master common_DSI3_block_registers_DSI_CFG);

   // DSI_CFG : SYNC_MASTER
   logic  SYNC_MASTER, SYNC_MASTER_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       SYNC_MASTER <= 1'b0;
     end
     else begin
       SYNC_MASTER <= SYNC_MASTER_nxt;
     end
   end

   always_comb begin
     SYNC_MASTER_nxt = SYNC_MASTER;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       SYNC_MASTER_nxt = data_in[6:6]; 
     end
   end

   assign common_DSI3_block_registers_DSI_CFG.SYNC_MASTER = SYNC_MASTER;

   // DSI_CFG : SYNC_PDCM
   logic  SYNC_PDCM, SYNC_PDCM_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       SYNC_PDCM <= 1'b1;
     end
     else begin
       SYNC_PDCM <= SYNC_PDCM_nxt;
     end
   end

   always_comb begin
     SYNC_PDCM_nxt = SYNC_PDCM;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       SYNC_PDCM_nxt = data_in[5:5]; 
     end
   end

   assign common_DSI3_block_registers_DSI_CFG.SYNC_PDCM = SYNC_PDCM;

   // DSI_CFG : CRC_EN
   logic  CRC_EN, CRC_EN_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       CRC_EN <= 1'b1;
     end
     else begin
       CRC_EN <= CRC_EN_nxt;
     end
   end

   always_comb begin
     CRC_EN_nxt = CRC_EN;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       CRC_EN_nxt = data_in[4:4]; 
     end
   end

   assign common_DSI3_block_registers_DSI_CFG.CRC_EN = CRC_EN;

   // DSI_CFG : BITTIME
   logic[1:0]  BITTIME, BITTIME_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       BITTIME <= 2'b0;
     end
     else begin
       BITTIME <= BITTIME_nxt;
     end
   end

   always_comb begin
     BITTIME_nxt = BITTIME;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       BITTIME_nxt = data_in[3:2]; 
     end
   end

   assign common_DSI3_block_registers_DSI_CFG.BITTIME = BITTIME;

   // DSI_CFG : CHIPTIME
   logic[1:0]  CHIPTIME, CHIPTIME_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       CHIPTIME <= 2'b1;
     end
     else begin
       CHIPTIME <= CHIPTIME_nxt;
     end
   end

   always_comb begin
     CHIPTIME_nxt = CHIPTIME;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       CHIPTIME_nxt = data_in[1:0]; 
     end
   end

   assign common_DSI3_block_registers_DSI_CFG.CHIPTIME = CHIPTIME;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {9'd0, SYNC_MASTER, SYNC_PDCM, CRC_EN, BITTIME, CHIPTIME} : '0;

   assign common_DSI3_block_registers_DSI_CFG.value = {9'd0, SYNC_MASTER, SYNC_PDCM, CRC_EN, BITTIME, CHIPTIME};

endmodule : common_DSI3_block_registers_DSI_CFG

/*###   DSI_TX_SHIFT   ######################################################*/
module common_DSI3_block_registers_DSI_TX_SHIFT #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   common_DSI3_block_registers_DSI_TX_SHIFT_if.master common_DSI3_block_registers_DSI_TX_SHIFT);

   // DSI_TX_SHIFT : SHIFT
   logic[6:0]  SHIFT, SHIFT_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       SHIFT <= 7'b100100;
     end
     else begin
       SHIFT <= SHIFT_nxt;
     end
   end

   always_comb begin
     SHIFT_nxt = SHIFT;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       SHIFT_nxt = data_in[6:0]; 
     end
   end

   assign common_DSI3_block_registers_DSI_TX_SHIFT.SHIFT = SHIFT;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {9'd0, SHIFT} : '0;

   assign common_DSI3_block_registers_DSI_TX_SHIFT.value = {9'd0, SHIFT};

endmodule : common_DSI3_block_registers_DSI_TX_SHIFT

/*###   SYNC_IDLE_REG   ######################################################*/
module common_DSI3_block_registers_SYNC_IDLE_REG #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   input logic[addr_width-1:0] addr,
   input logic           rd,
   output logic[15:0]     data_out,
   common_DSI3_block_registers_SYNC_IDLE_REG_if.master common_DSI3_block_registers_SYNC_IDLE_REG);

   // SYNC_IDLE_REG : PIN
   logic  PIN;


   always_comb begin
       PIN = common_DSI3_block_registers_SYNC_IDLE_REG.PIN_in;
   end

   assign common_DSI3_block_registers_SYNC_IDLE_REG.PIN = PIN;

   // SYNC_IDLE_REG : DSI
   logic[1:0]  DSI;


   always_comb begin
       DSI = common_DSI3_block_registers_SYNC_IDLE_REG.DSI_in;
   end

   assign common_DSI3_block_registers_SYNC_IDLE_REG.DSI = DSI;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {PIN, 13'd0, DSI} : '0;

   assign common_DSI3_block_registers_SYNC_IDLE_REG.value = {PIN, 13'd0, DSI};

endmodule : common_DSI3_block_registers_SYNC_IDLE_REG

/*###   CRM_TIME   ######################################################*/
module common_DSI3_block_registers_CRM_TIME #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   common_DSI3_block_registers_CRM_TIME_if.master common_DSI3_block_registers_CRM_TIME);

   // CRM_TIME : TIME
   logic[10:0]  TIME, TIME_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       TIME <= 11'b111000010;
     end
     else begin
       TIME <= TIME_nxt;
     end
   end

   always_comb begin
     TIME_nxt = TIME;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       TIME_nxt = data_in[10:0]; 
     end
   end

   assign common_DSI3_block_registers_CRM_TIME.TIME = TIME;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {5'd0, TIME} : '0;

   assign common_DSI3_block_registers_CRM_TIME.value = {5'd0, TIME};

endmodule : common_DSI3_block_registers_CRM_TIME

/*###   CRM_TIME_NR   ######################################################*/
module common_DSI3_block_registers_CRM_TIME_NR #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic[15:0]     data_in,
   input logic           wr,
   input logic           rd,
   output logic[15:0]     data_out,
   common_DSI3_block_registers_CRM_TIME_NR_if.master common_DSI3_block_registers_CRM_TIME_NR);

   // CRM_TIME_NR : TIME
   logic[10:0]  TIME, TIME_nxt;

   always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
     if (clk_rst.rstn == 1'b0)  begin
       TIME <= 11'b100101100;
     end
     else begin
       TIME <= TIME_nxt;
     end
   end

   always_comb begin
     TIME_nxt = TIME;
     if ((wr == 1'b1) && (reg_addr[addr_width-1:0] == addr )) begin
       TIME_nxt = data_in[10:0]; 
     end
   end

   assign common_DSI3_block_registers_CRM_TIME_NR.TIME = TIME;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {5'd0, TIME} : '0;

   assign common_DSI3_block_registers_CRM_TIME_NR.value = {5'd0, TIME};

endmodule : common_DSI3_block_registers_CRM_TIME_NR

/*###   Registers   ######################################################*/
module common_DSI3_block_registers #(
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
   common_DSI3_block_registers_DSI_ENABLE_if.master common_DSI3_block_registers_DSI_ENABLE,
   common_DSI3_block_registers_DSI_CFG_if.master common_DSI3_block_registers_DSI_CFG,
   common_DSI3_block_registers_DSI_TX_SHIFT_if.master common_DSI3_block_registers_DSI_TX_SHIFT,
   common_DSI3_block_registers_SYNC_IDLE_REG_if.master common_DSI3_block_registers_SYNC_IDLE_REG,
   common_DSI3_block_registers_CRM_TIME_if.master common_DSI3_block_registers_CRM_TIME,
   common_DSI3_block_registers_CRM_TIME_NR_if.master common_DSI3_block_registers_CRM_TIME_NR
);

   logic[15:0] data_out_DSI_ENABLE, data_out_DSI_CFG, data_out_DSI_TX_SHIFT, data_out_SYNC_IDLE_REG, data_out_CRM_TIME, data_out_CRM_TIME_NR;

   common_DSI3_block_registers_DSI_ENABLE #( .reg_addr (base_addr + 'h91), .addr_width(addr_width) ) i_common_DSI3_block_registers_DSI_ENABLE ( .data_out (data_out_DSI_ENABLE), .*);
   common_DSI3_block_registers_DSI_CFG #( .reg_addr (base_addr + 'h92), .addr_width(addr_width) ) i_common_DSI3_block_registers_DSI_CFG ( .data_out (data_out_DSI_CFG), .*);
   common_DSI3_block_registers_DSI_TX_SHIFT #( .reg_addr (base_addr + 'h94), .addr_width(addr_width) ) i_common_DSI3_block_registers_DSI_TX_SHIFT ( .data_out (data_out_DSI_TX_SHIFT), .*);
   common_DSI3_block_registers_SYNC_IDLE_REG #( .reg_addr (base_addr + 'h95), .addr_width(addr_width) ) i_common_DSI3_block_registers_SYNC_IDLE_REG ( .data_out (data_out_SYNC_IDLE_REG), .*);
   common_DSI3_block_registers_CRM_TIME #( .reg_addr (base_addr + 'h98), .addr_width(addr_width) ) i_common_DSI3_block_registers_CRM_TIME ( .data_out (data_out_CRM_TIME), .*);
   common_DSI3_block_registers_CRM_TIME_NR #( .reg_addr (base_addr + 'h99), .addr_width(addr_width) ) i_common_DSI3_block_registers_CRM_TIME_NR ( .data_out (data_out_CRM_TIME_NR), .*);

   // output data assignment
   assign data_out = data_out_DSI_ENABLE | data_out_DSI_CFG | data_out_DSI_TX_SHIFT | data_out_SYNC_IDLE_REG | data_out_CRM_TIME | data_out_CRM_TIME_NR;

endmodule : common_DSI3_block_registers
