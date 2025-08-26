
`timescale 1ns/10ps

module utils_sram_parity #(
    parameter ADDR_WIDTH    = 10,
    parameter PART_WIDTH    = 8,
    parameter PART_PAR_BITS = 1,
    parameter PROTECT_ADDR  = 0
  )(
    input                         clk,
    input                         nrst,

    input                         parity_swap,
    output logic                  parity_event,
    input     [PART_PAR_BITS-1:0] par_val,
    input                         par_sel,

    input                         ce,
    input                         oe,
    input        [ADDR_WIDTH-1:0] addr,
    input        [PART_WIDTH-1:0] wdata,
    output logic [PART_WIDTH-1:0] rdata,

    output logic [PART_WIDTH+PART_PAR_BITS-1:0] wdata_sram, // SRAM IP write data
    input        [PART_WIDTH+PART_PAR_BITS-1:0] rdata_sram  // SRAM IP read data
  );

  logic                  rdata_cycle;
  logic [ADDR_WIDTH-1:0] prev_addr;

  always @(negedge nrst or posedge clk)
  begin
    if (!nrst) begin
      rdata_cycle <= 1'b0;
      prev_addr <= '0;
    end
    else begin
      rdata_cycle <= ce & oe;
      prev_addr <= addr;
    end
  end

  logic rdata_parity;
  logic raddr_parity;
  wire  wdata_parity = ^wdata;
  wire  waddr_parity = ^addr;

  always @(negedge nrst or posedge clk)
  begin
    if (!nrst) begin
      parity_event <= 1'b0;
    end
    else begin
      parity_event <= 1'b0;

      if (rdata_cycle) begin
        if (rdata_parity != ^rdata) begin
          parity_event <= 1'b1;
        end
        if (PROTECT_ADDR) begin
          if (raddr_parity != ^prev_addr) begin
            parity_event <= 1'b1;
          end
        end
      end
    end
  end

  //==========================================================================

  logic [PART_WIDTH+PART_PAR_BITS-1:0] wdata_sram_pre_swap;

  always_comb
  begin
    wdata_sram_pre_swap = '0;
    wdata_sram_pre_swap[PART_WIDTH-1:0] = wdata;

    if (PROTECT_ADDR) begin
      wdata_sram_pre_swap[PART_WIDTH+PART_PAR_BITS-2] = wdata_parity;
      wdata_sram_pre_swap[PART_WIDTH+PART_PAR_BITS-1] = waddr_parity;
    end
    else begin
      wdata_sram_pre_swap[PART_WIDTH+PART_PAR_BITS-1] = wdata_parity;
    end
  end

  always_comb
  begin
    wdata_sram = wdata_sram_pre_swap;

    if (parity_swap) begin
      // data LSB(s) and parity bit(s) swapped
      wdata_sram[         0 +: PART_PAR_BITS] = wdata_sram_pre_swap[PART_WIDTH +: PART_PAR_BITS];
      wdata_sram[PART_WIDTH +: PART_PAR_BITS] = wdata_sram_pre_swap[         0 +: PART_PAR_BITS];
    end

    if (par_sel) begin
      wdata_sram[PART_WIDTH +: PART_PAR_BITS] = par_val;
    end
  end

  //==========================================================================

  logic [PART_WIDTH+PART_PAR_BITS-1:0] rdata_sram_post_swap;

  always_comb
  begin
    rdata_sram_post_swap = rdata_sram;

    if (parity_swap) begin
      // data LSB(s) and parity bit(s) swapped
      rdata_sram_post_swap[         0 +: PART_PAR_BITS] = rdata_sram[PART_WIDTH +: PART_PAR_BITS];
      rdata_sram_post_swap[PART_WIDTH +: PART_PAR_BITS] = rdata_sram[         0 +: PART_PAR_BITS];
    end
  end

  always_comb
  begin
    rdata        = rdata_sram_post_swap[PART_WIDTH-1:0];
    rdata_parity = 1'b0;
    raddr_parity = 1'b0;

    if (PROTECT_ADDR) begin
      rdata_parity = rdata_sram_post_swap[PART_WIDTH+PART_PAR_BITS-2];
      raddr_parity = rdata_sram_post_swap[PART_WIDTH+PART_PAR_BITS-1];
    end
    else begin
      rdata_parity = rdata_sram_post_swap[PART_WIDTH+PART_PAR_BITS-1];
    end
  end

  `ifdef SVA
  //=========================================================================
  // SV assertions
  //=========================================================================

// VCS coverage off
  reg time_zero;

  initial begin
    time_zero = 1'b1;
    #1;
    time_zero = 1'b0;
  end
// VCS coverage on

  clocking cb @(posedge clk);

    property parity_swap_never_x_p;
      disable iff (time_zero) !$isunknown(parity_swap);
    endproperty

    property par_val_never_x_p;
      disable iff (time_zero) !$isunknown(par_val);
    endproperty

    property par_sel_never_x_p;
      disable iff (time_zero) !$isunknown(par_sel);
    endproperty

  endclocking

  parity_swap_never_x : assert property (cb.parity_swap_never_x_p) else $fatal;
  par_val_never_x     : assert property (cb.par_val_never_x_p    ) else $fatal;
  par_sel_never_x     : assert property (cb.par_sel_never_x_p    ) else $fatal;

  `endif

endmodule

