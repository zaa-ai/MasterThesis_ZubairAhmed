
`timescale 1ns/1ns

module utils_sram_bist_march_22n #(  // BIST type: XY MARCH 22N
    parameter ABITS      = 2,
    parameter APARTS     = 4,
    parameter DEPTH      = 256,
    parameter ADDR_WIDTH = 10,
    parameter PART_WIDTH = 8
  )(
    input                       clk,
    input                       nrst,

    bist_if.sp                  bist,
    output                      bist_run,

    output reg                  ce,
    output reg                  we,
    output                      oe,
    output reg [ADDR_WIDTH-1:0] addr,
    output reg [PART_WIDTH-1:0] wdata,
    input      [PART_WIDTH-1:0] rdata
  );

  `include "vlog_functions_inc.sv"

  localparam MAX_ADDR = ((DEPTH - 1) << ABITS) + APARTS - 1;

  import bist_pkg::*;

  wire bist_bitwise;
  wire bist_four_6n;

  utils_sync_level utils_sync_level_inst[2:0](
    .in_val   ({bist.run, bist.bitwise, bist.four_6n}),
    .out_clk  (clk),
    .out_nres (nrst),
    .out_val  ({bist_run, bist_bitwise, bist_four_6n})
  );

  wire [PART_WIDTH-1:0] pattern_p     = { (PART_WIDTH + 1) / 2 {1'h1, 1'h0}};
  wire [PART_WIDTH-1:0] pattern_n     = { (PART_WIDTH + 1) / 2 {1'h0, 1'h1}};
  wire [PART_WIDTH-1:0] pattern_0     = {  PART_WIDTH          {      1'b0}};
  wire [PART_WIDTH-1:0] pattern_1     = {  PART_WIDTH          {      1'b1}};
  wire [PART_WIDTH-1:0] pattern_6N_01 = {  PART_WIDTH          {      1'b0}};
  wire [PART_WIDTH-1:0] pattern_6N_11 = {  PART_WIDTH          {      1'b1}};
  wire [PART_WIDTH-1:0] pattern_6N_02 = { (PART_WIDTH + 7) / 8 {4'h0, 4'hF}};
  wire [PART_WIDTH-1:0] pattern_6N_12 = { (PART_WIDTH + 7) / 8 {4'hF, 4'h0}};
  wire [PART_WIDTH-1:0] pattern_6N_03 = { (PART_WIDTH + 3) / 4 {2'h0, 2'h3}};
  wire [PART_WIDTH-1:0] pattern_6N_13 = { (PART_WIDTH + 3) / 4 {2'h3, 2'h0}};
  wire [PART_WIDTH-1:0] pattern_6N_04 = { (PART_WIDTH + 1) / 2 {1'h0, 1'h1}};
  wire [PART_WIDTH-1:0] pattern_6N_14 = { (PART_WIDTH + 1) / 2 {1'h1, 1'h0}};

  typedef enum logic [4:0] {
    RP  = 5'd0,  // R
    WP  = 5'd1,  // W
    RN  = 5'd2,  // Rbar
    WN  = 5'd3,  // Wbar
    R0  = 5'd4,  // R0
    W0  = 5'd5,  // W0
    R1  = 5'd6,  // R1
    W1  = 5'd7,  // W1

    R01 = 5'd8,
    W01 = 5'd9,
    R11 = 5'd10,
    W11 = 5'd11,

    R02 = 5'd12,
    W02 = 5'd13,
    R12 = 5'd14,
    W12 = 5'd15,

    R03 = 5'd16,
    W03 = 5'd17,
    R13 = 5'd18,
    W13 = 5'd19,

    R04 = 5'd20,
    W04 = 5'd21,
    R14 = 5'd22,
    W14 = 5'd23
  } access_type_t;

  typedef enum logic [1:0] {
    DN = 2'd0,  // down word-wise
    UP = 2'd1,  // up word-wise
    UB = 2'd2   // up bit-wise
  } direction_t;

  typedef enum logic [3:0] {
    PAT_P = 4'd0,
    PAT_N = 4'd1,
    PAT_0 = 4'd2,
    PAT_1 = 4'd3,

    PAT_6N_01 = 4'd4,
    PAT_6N_11 = 4'd5,
    PAT_6N_02 = 4'd6,
    PAT_6N_12 = 4'd7,
    PAT_6N_03 = 4'd8,
    PAT_6N_13 = 4'd9,
    PAT_6N_04 = 4'd10,
    PAT_6N_14 = 4'd11
  } pat_sel_t;

  typedef enum logic [4:0] {
    ST_IDLE              = 5'd0,
    ST_WAIT              = 5'd1,

    ST_UP_WP             = 5'd2,
    ST_DN_RP_WN          = 5'd3,
    ST_UP_RN_WP_RP_RP_WN = 5'd4,
    ST_DN_RN_WP          = 5'd5,
    ST_UP_RP_WN_RN_RN_WP = 5'd6,
    ST_UP_RP             = 5'd7,
    ST_UP_W0             = 5'd8,
    ST_UP_R0_W1          = 5'd9,
    ST_DN_R1_W0          = 5'd10,
    ST_UP_R0             = 5'd11,

    ST_UP_W1B_R1B        = 5'd12,  // fill bitwise 1 bits and verify
    ST_UP_W0B_R0B        = 5'd13,  // fill bitwise 0 bits and verify

    ST_UP_6N_W01         = 5'd14,
    ST_UP_6N_R01_W11     = 5'd15,
    ST_DN_6N_R11_W01_R01 = 5'd16,
    ST_UP_6N_W02         = 5'd17,
    ST_UP_6N_R02_W12     = 5'd18,
    ST_DN_6N_R12_W02_R02 = 5'd19,
    ST_UP_6N_W03         = 5'd20,
    ST_UP_6N_R03_W13     = 5'd21,
    ST_DN_6N_R13_W03_R03 = 5'd22,
    ST_UP_6N_W04         = 5'd23,
    ST_UP_6N_R04_W14     = 5'd24,
    ST_DN_6N_R14_W04_R04 = 5'd25,

    ST_FINISH            = 5'd26
  } step_t;

  typedef logic [2:0] sub_step_t;

  step_t      step;
  sub_step_t  sub_step;
  pat_sel_t   data_sel;
  pat_sel_t   rdata_sel;
  direction_t up;
  logic       bitwise;
  logic       rbitwise;

  logic [num2width(PART_WIDTH-1)-1:0] bit_counter;

  task mem_access(
    input access_type_t t,  // type of access
    input sub_step_t    s   // sub_step
  );
  begin
    ce <= 1'b1;
    we <= 1'b0;
    data_sel <= PAT_P;
    case (t)
      WP,  WN,  W0,  W1  : we <= 1'b1;
      W01, W11, W02, W12 : we <= 1'b1;
      W03, W13, W04, W14 : we <= 1'b1;
    endcase
    case (t)
      RP, WP : data_sel <= PAT_P;
      RN, WN : data_sel <= PAT_N;
      R0, W0 : data_sel <= PAT_0;
      R1, W1 : data_sel <= PAT_1;

      R01, W01 : data_sel <= PAT_6N_01;
      R11, W11 : data_sel <= PAT_6N_11;
      R02, W02 : data_sel <= PAT_6N_02;
      R12, W12 : data_sel <= PAT_6N_12;
      R03, W03 : data_sel <= PAT_6N_03;
      R13, W13 : data_sel <= PAT_6N_13;
      R04, W04 : data_sel <= PAT_6N_04;
      R14, W14 : data_sel <= PAT_6N_14;
    endcase
    sub_step <= s;
  end
  endtask

  task init_step;
  begin
    ce          <= 1'b0;
    we          <= 1'b0;
    addr        <= '0;
    up          <= DN;
    data_sel    <= PAT_P;
    sub_step    <= 2'd0;
    bitwise     <= 1'b0;
    bit_counter <= '0;
  end
  endtask

  task next_step(
    input direction_t   u,  // up
    input access_type_t t,  // type of access
    input sub_step_t    s   // sub_step
  );
  begin
    addr        <= (u == DN) ? MAX_ADDR : '0;
    up          <= u;
    step        <= step_t'(step + 5'd1);
    bitwise     <= (u == UB) ? 1'b1 : 1'b0;
    bit_counter <= (u == UB) ? PART_WIDTH-1 : '0;
    mem_access(t, s);
  end
  endtask

  logic [PART_WIDTH-1:0] pattern_b;
  logic [PART_WIDTH-1:0] rpattern_b;

  wire  addr_n = addr[ABITS];
  logic raddr_n;

  always_comb
  begin
    pattern_b = {PART_WIDTH{1'b1}} >> bit_counter;
    if (step == ST_UP_W0B_R0B) begin
      pattern_b = {PART_WIDTH{1'b1}} << (PART_WIDTH - bit_counter);
    end
  end

  logic  cmp_e;
  logic  compare_ok;
  logic  step_finished;

  always_comb
  begin
    compare_ok = 1'b0;
    if (cmp_e) begin
      if (rbitwise) begin
        compare_ok = (rdata == rpattern_b) ? 1'b1 : 1'b0;
      end
      else begin
        case (rdata_sel)
          PAT_P : compare_ok = (rdata == (raddr_n ? pattern_n : pattern_p)) ? 1'b1 : 1'b0;
          PAT_N : compare_ok = (rdata == (raddr_n ? pattern_p : pattern_n)) ? 1'b1 : 1'b0;
          PAT_0 : compare_ok = (rdata == pattern_0) ? 1'b1 : 1'b0;
          PAT_1 : compare_ok = (rdata == pattern_1) ? 1'b1 : 1'b0;

          PAT_6N_01 : compare_ok = (rdata == pattern_6N_01) ? 1'b1 : 1'b0;
          PAT_6N_11 : compare_ok = (rdata == pattern_6N_11) ? 1'b1 : 1'b0;
          PAT_6N_02 : compare_ok = (rdata == pattern_6N_02) ? 1'b1 : 1'b0;
          PAT_6N_12 : compare_ok = (rdata == pattern_6N_12) ? 1'b1 : 1'b0;
          PAT_6N_03 : compare_ok = (rdata == pattern_6N_03) ? 1'b1 : 1'b0;
          PAT_6N_13 : compare_ok = (rdata == pattern_6N_13) ? 1'b1 : 1'b0;
          PAT_6N_04 : compare_ok = (rdata == pattern_6N_04) ? 1'b1 : 1'b0;
          PAT_6N_14 : compare_ok = (rdata == pattern_6N_14) ? 1'b1 : 1'b0;
        endcase
      end
    end
  end

  always_comb
  begin
    step_finished = 1'b0;
    if (!bit_counter && !sub_step) begin
      if (up == DN) step_finished = (addr ==       '0) ? 1'b1 : 1'b0;
      else          step_finished = (addr == MAX_ADDR) ? 1'b1 : 1'b0;
    end
  end

  always_comb
  begin
    wdata = pattern_b;
    if (!bitwise) begin
      case (data_sel)
        PAT_P : wdata = addr_n ? pattern_n : pattern_p;
        PAT_N : wdata = addr_n ? pattern_p : pattern_n;
        PAT_0 : wdata = pattern_0;
        PAT_1 : wdata = pattern_1;

        PAT_6N_01 : wdata = pattern_6N_01;
        PAT_6N_11 : wdata = pattern_6N_11;
        PAT_6N_02 : wdata = pattern_6N_02;
        PAT_6N_12 : wdata = pattern_6N_12;
        PAT_6N_03 : wdata = pattern_6N_03;
        PAT_6N_13 : wdata = pattern_6N_13;
        PAT_6N_04 : wdata = pattern_6N_04;
        PAT_6N_14 : wdata = pattern_6N_14;
      endcase
    end
  end

  function [ADDR_WIDTH-1:0] decr_addr;
  begin
    decr_addr = addr - 1;
    if (ABITS) begin
      if (!addr[(ABITS ? ABITS : 1)-1:0]) begin
        decr_addr = (((addr >> ABITS) - 1) << ABITS) + APARTS - 1;
      end
    end
  end
  endfunction

  function [ADDR_WIDTH-1:0] incr_addr;
  begin
    incr_addr = addr + 1;
    if (ABITS) begin
      if (addr[(ABITS ? ABITS : 1)-1:0] >= (APARTS - 1)) begin
        incr_addr = (((addr >> ABITS) + 1) << ABITS);
      end
    end
  end
  endfunction

  assign oe = ce & ~we;

  always_ff @(negedge nrst or posedge clk)
  begin
    if (!nrst) begin
      init_step;
      cmp_e      <= 1'b0;
      rdata_sel  <= PAT_P;
      raddr_n    <= 1'b0;
      rbitwise   <= 1'b0;
      rpattern_b <= '0;
      bist.state <= BIST_INIT;
      step       <= ST_IDLE;
    end
    else begin
      if (!sub_step) begin
        if (bit_counter) begin
          bit_counter <= bit_counter - 1;
        end
        else begin
          if (bitwise) begin
            bit_counter <= PART_WIDTH-1;
          end
          if (up == DN) addr <= (addr >       '0) ? decr_addr() :       '0;
          else          addr <= (addr < MAX_ADDR) ? incr_addr() : MAX_ADDR;
        end
      end
      cmp_e <= oe;
      rdata_sel <= data_sel;
      raddr_n <= addr_n;
      rbitwise <= bitwise;
      rpattern_b <= pattern_b;

      case (step)
        ST_IDLE : begin
          if (!bist_run) begin
            bist.state <= BIST_INIT;
            step <= ST_WAIT;
          end
        end
        ST_WAIT : begin
          if (bist_run) begin
            bist.state <= BIST_BUSY;
            next_step(UP, WP, 3'd0);
          end
        end

        ST_UP_WP : begin
          if (sub_step == 3'd0) mem_access(WP, 3'd0);
          if (step_finished) next_step(DN, RP, 3'd1);
        end
        ST_DN_RP_WN : begin
          if (sub_step == 3'd1) mem_access(WN, 3'd0);
          if (sub_step == 3'd0) mem_access(RP, 3'd1);
          if (step_finished) next_step(UP, RN, 3'd4);
        end
        ST_UP_RN_WP_RP_RP_WN : begin
          if (sub_step == 3'd4) mem_access(WP, 3'd3);
          if (sub_step == 3'd3) mem_access(RP, 3'd2);
          if (sub_step == 3'd2) mem_access(RP, 3'd1);
          if (sub_step == 3'd1) mem_access(WN, 3'd0);
          if (sub_step == 3'd0) mem_access(RN, 3'd4);
          if (step_finished) next_step(DN, RN, 3'd1);
        end
        ST_DN_RN_WP : begin
          if (sub_step == 3'd1) mem_access(WP, 3'd0);
          if (sub_step == 3'd0) mem_access(RN, 3'd1);
          if (step_finished) next_step(UP, RP, 3'd4);
        end
        ST_UP_RP_WN_RN_RN_WP : begin
          if (sub_step == 3'd4) mem_access(WN, 3'd3);
          if (sub_step == 3'd3) mem_access(RN, 3'd2);
          if (sub_step == 3'd2) mem_access(RN, 3'd1);
          if (sub_step == 3'd1) mem_access(WP, 3'd0);
          if (sub_step == 3'd0) mem_access(RP, 3'd4);
          if (step_finished) next_step(UP, RP, 3'd0);
        end
        ST_UP_RP : begin
          if (sub_step == 3'd0) mem_access(RP, 3'd0);
          if (step_finished) next_step(UP, W0, 3'd0);
        end
        ST_UP_W0 : begin
          if (sub_step == 3'd0) mem_access(W0, 3'd0);
          if (step_finished) next_step(UP, R0, 3'd1);
        end
        ST_UP_R0_W1 : begin
          if (sub_step == 3'd1) mem_access(W1, 3'd0);
          if (sub_step == 3'd0) mem_access(R0, 3'd1);
          if (step_finished) next_step(DN, R1, 3'd1);
        end
        ST_DN_R1_W0 : begin
          if (sub_step == 3'd1) mem_access(W0, 3'd0);
          if (sub_step == 3'd0) mem_access(R1, 3'd1);
          if (step_finished) next_step(UP, R0, 3'd0);
        end
        ST_UP_R0 : begin
          if (sub_step == 3'd0) mem_access(R0, 3'd0);
          if (step_finished) begin
            if (bist_bitwise) begin
              next_step(UB, WN, 3'd1);
              step <= ST_UP_W1B_R1B;
            end
            else if (bist_four_6n) begin
              next_step(UP, W01, 3'd0);
              step <= ST_UP_6N_W01;
            end
            else begin
              init_step;
              step <= ST_FINISH;
            end
          end
        end

        ST_UP_W1B_R1B : begin
          if (sub_step == 3'd1) mem_access(RN, 3'd0);
          if (sub_step == 3'd0) mem_access(WN, 3'd1);
          if (step_finished) next_step(UB, WP, 3'd1);
        end
        ST_UP_W0B_R0B : begin
          if (sub_step == 3'd1) mem_access(RP, 3'd0);
          if (sub_step == 3'd0) mem_access(WP, 3'd1);
          if (step_finished) begin
            if (bist_four_6n) begin
              next_step(UP, W01, 3'd0);
              step <= ST_UP_6N_W01;
            end
            else begin
              init_step;
              step <= ST_FINISH;
            end
          end
        end

        ST_UP_6N_W01 : begin
          if (sub_step == 3'd0) mem_access(W01, 3'd0);
          if (step_finished) next_step(UP, R01, 3'd1);
        end
        ST_UP_6N_R01_W11 : begin
          if (sub_step == 3'd1) mem_access(W11, 3'd0);
          if (sub_step == 3'd0) mem_access(R01, 3'd1);
          if (step_finished) next_step(DN, R11, 3'd2);
        end
        ST_DN_6N_R11_W01_R01 : begin
          if (sub_step == 3'd2) mem_access(W01, 3'd1);
          if (sub_step == 3'd1) mem_access(R01, 3'd0);
          if (sub_step == 3'd0) mem_access(R11, 3'd2);
          if (step_finished) next_step(UP, W02, 3'd0);
        end

        ST_UP_6N_W02 : begin
          if (sub_step == 3'd0) mem_access(W02, 3'd0);
          if (step_finished) next_step(UP, R02, 3'd1);
        end
        ST_UP_6N_R02_W12 : begin
          if (sub_step == 3'd1) mem_access(W12, 3'd0);
          if (sub_step == 3'd0) mem_access(R02, 3'd1);
          if (step_finished) next_step(DN, R12, 3'd2);
        end
        ST_DN_6N_R12_W02_R02 : begin
          if (sub_step == 3'd2) mem_access(W02, 3'd1);
          if (sub_step == 3'd1) mem_access(R02, 3'd0);
          if (sub_step == 3'd0) mem_access(R12, 3'd2);
          if (step_finished) next_step(UP, W03, 3'd0);
        end

        ST_UP_6N_W03 : begin
          if (sub_step == 3'd0) mem_access(W03, 3'd0);
          if (step_finished) next_step(UP, R03, 3'd1);
        end
        ST_UP_6N_R03_W13 : begin
          if (sub_step == 3'd1) mem_access(W13, 3'd0);
          if (sub_step == 3'd0) mem_access(R03, 3'd1);
          if (step_finished) next_step(DN, R13, 3'd2);
        end
        ST_DN_6N_R13_W03_R03 : begin
          if (sub_step == 3'd2) mem_access(W03, 3'd1);
          if (sub_step == 3'd1) mem_access(R03, 3'd0);
          if (sub_step == 3'd0) mem_access(R13, 3'd2);
          if (step_finished) next_step(UP, W04, 3'd0);
        end

        ST_UP_6N_W04 : begin
          if (sub_step == 3'd0) mem_access(W04, 3'd0);
          if (step_finished) next_step(UP, R04, 3'd1);
        end
        ST_UP_6N_R04_W14 : begin
          if (sub_step == 3'd1) mem_access(W14, 3'd0);
          if (sub_step == 3'd0) mem_access(R04, 3'd1);
          if (step_finished) next_step(DN, R14, 3'd2);
        end
        ST_DN_6N_R14_W04_R04 : begin
          if (sub_step == 3'd2) mem_access(W04, 3'd1);
          if (sub_step == 3'd1) mem_access(R04, 3'd0);
          if (sub_step == 3'd0) mem_access(R14, 3'd2);
          if (step_finished) begin
            init_step;
            step <= ST_FINISH;
          end
        end

        ST_FINISH : begin
          if (compare_ok) begin
            bist.state <= BIST_PASS;
            step <= ST_IDLE;
          end
        end
      endcase

      if (cmp_e && !compare_ok) begin
        init_step;
        bist.state <= BIST_FAIL;
        step <= ST_IDLE;
      end
    end
  end

  `ifdef SVA
  //=========================================================================
  // SV assertions
  //=========================================================================

  integer up_w_count;
  integer up_r_count;
  integer dn_w_count;
  integer dn_r_count;
  integer cmp_count;

  always_ff @(negedge nrst or posedge clk)
  begin
    if (!nrst) begin
      up_w_count <= 0;
      up_r_count <= 0;
      dn_w_count <= 0;
      dn_r_count <= 0;
      cmp_count  <= 0;
    end
    else begin
      if (ce) begin
        if (up == DN) begin
          if (we) dn_w_count++;
          else    dn_r_count++;
        end
        else begin
          if (we) up_w_count++;
          else    up_r_count++;
        end
      end
      if (cmp_e) begin
        cmp_count++;
      end
      if (step == ST_WAIT) begin
        up_w_count <= 0;
        up_r_count <= 0;
        dn_w_count <= 0;
        dn_r_count <= 0;
        cmp_count  <= 0;
      end
    end
  end

  integer up_w_count_expected;
  integer up_r_count_expected;
  integer dn_w_count_expected;
  integer dn_r_count_expected;

  always_comb
  begin
    up_w_count_expected = (DEPTH * APARTS) * 7;
    up_r_count_expected = (DEPTH * APARTS) * 9;
    dn_w_count_expected = (DEPTH * APARTS) * 3;
    dn_r_count_expected = (DEPTH * APARTS) * 3;

    if (bist_bitwise) begin
      up_w_count_expected += (DEPTH * APARTS) * (2 * PART_WIDTH);
      up_r_count_expected += (DEPTH * APARTS) * (2 * PART_WIDTH);
    end
    if (bist_four_6n) begin
      up_w_count_expected += (DEPTH * APARTS) * 8;
      up_r_count_expected += (DEPTH * APARTS) * 4;
      dn_w_count_expected += (DEPTH * APARTS) * 4;
      dn_r_count_expected += (DEPTH * APARTS) * 8;
    end
  end

  clocking cb @(posedge clk);

    property bist_run_never_x_p;
      !$isunknown(bist.run);
    endproperty

    property bist_bitwise_never_x_p;
      !$isunknown(bist.bitwise);
    endproperty

    property bist_four_6n_never_x_p;
      !$isunknown(bist.four_6n);
    endproperty

    property check_up_w_count_p;
      disable iff (!bist_run) (bist.state == BIST_PASS) |-> (up_w_count == up_w_count_expected);
    endproperty

    property check_up_r_count_p;
      disable iff (!bist_run) (bist.state == BIST_PASS) |-> (up_r_count == up_r_count_expected);
    endproperty

    property check_dn_w_count_p;
      disable iff (!bist_run) (bist.state == BIST_PASS) |-> (dn_w_count == dn_w_count_expected);
    endproperty

    property check_dn_r_count_p;
      disable iff (!bist_run) (bist.state == BIST_PASS) |-> (dn_r_count == dn_r_count_expected);
    endproperty

    property check_cmp_count_p;
      disable iff (!bist_run) (bist.state == BIST_PASS) |-> (cmp_count == (up_r_count_expected + dn_r_count_expected));
    endproperty

  endclocking

  bist_run_never_x     : assert property (cb.bist_run_never_x_p    ) else $fatal;
  bist_bitwise_never_x : assert property (cb.bist_bitwise_never_x_p) else $fatal;
  bist_four_6n_never_x : assert property (cb.bist_four_6n_never_x_p) else $fatal;
  check_up_w_count     : assert property (cb.check_up_w_count_p    ) else $fatal;
  check_up_r_count     : assert property (cb.check_up_r_count_p    ) else $fatal;
  check_dn_w_count     : assert property (cb.check_dn_w_count_p    ) else $fatal;
  check_dn_r_count     : assert property (cb.check_dn_r_count_p    ) else $fatal;
  check_cmp_count      : assert property (cb.check_cmp_count_p     ) else $fatal;

  `endif

endmodule

