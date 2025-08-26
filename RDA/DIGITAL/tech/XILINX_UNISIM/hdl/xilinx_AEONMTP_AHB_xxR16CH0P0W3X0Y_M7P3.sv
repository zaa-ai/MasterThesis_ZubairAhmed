
`timescale 1ns/1ns

module xilinx_AEONMTP_AHB_xxR16CH0P0W3X0Y_M7P3 #(
    parameter TRACE_EN_PARAM     = 0,
    parameter MEMORY_STATE_PARAM = 0,
    parameter MEMORY_FILE_PARAM  = "aeonmtp.dat",
    parameter WORDS              = 80,
    parameter ADDR_WIDTH         = num2width(WORDS-1)
  )(
    input             clk24,
    input             nrst,

    input             IP_EN,
    input             CP_ENABLE,
    input             READ,
    input             PROG,
    input             ERASE,
    input  [ADDR_WIDTH-1:0] ADDR,
    input      [15:0] DIN,
    output reg [15:0] DOUT,
    output            READY,

    // test mode signals ...
    input       [2:0] MARGIN_TRIM,
    input             TEST_BULK_EVEN_EN,
    input             TEST_BULK_ODD_EN,
    input             TEST_CELL_CURRENT_MON_EN,
    input             TEST_OSC_MON_EN,
    input             TEST_MARGIN_READ_EN,

    // test outputs ...
    output      [1:0] TEST_CELL_CURRENT_MON,
    output            TEST_OSC_CLK_MON
  );

  `include "vlog_functions_inc.sv"

  reg      [15:0] mem[0:WORDS-1];
  reg [WORDS-1:0] erased;

  integer n;

  reg [31:0] counter;

  reg ERASE_last;
  reg PROG_last;
  reg READ_last;
  reg fail;

  always @(negedge nrst or posedge clk24)
  begin
    if (!nrst) begin
      counter <= 32'd0;
      ERASE_last <= 1'b0;
      PROG_last <= 1'b0;
      READ_last <= 1'b0;
      for (n = 0; n < WORDS; n = n + 1) begin
        // mem[n] <= 16'hdead; explicitily do not reset mem area to keep content after reset! keep this entry as comment
        erased[n] <= 1'b0;
      end
      DOUT <= 16'hdead;
      fail <= 1'b0;
    end
    else begin
      ERASE_last <= ERASE;
      PROG_last <= PROG;
      READ_last <= READ;

      if (counter) begin
        counter <= counter - 32'd1;
      end

      if (!ERASE && ERASE_last) begin
        counter <= 32'd0;
      end
      if (!PROG && PROG_last) begin
        counter <= 32'd0;
      end
      if (!READ && READ_last) begin
        counter <= 32'd0;
      end

      if (CP_ENABLE && ERASE && !ERASE_last) begin
        counter <= 32'd96000;  // 4ms at 24MHz
        if (ADDR >= WORDS) begin
          fail <= 1'b1;
        end
      end
      if (CP_ENABLE && PROG && !PROG_last) begin
        counter <= 32'd96000;  // 4ms at 24MHz
        if (ADDR >= WORDS) begin
          fail <= 1'b1;
        end
      end
      if (READ && !READ_last) begin
        counter <= 32'd6;  // 250ns at 24MHz
        if (ADDR >= WORDS) begin
          fail <= 1'b1;
        end
      end

      if (counter == 32'd1) begin
        if (CP_ENABLE && ERASE) begin
          if (ADDR < WORDS) begin
            mem[{ADDR[ADDR_WIDTH-1:1], 1'b0}] <= 16'hdead;
            mem[{ADDR[ADDR_WIDTH-1:1], 1'b1}] <= 16'hdead;
            erased[{ADDR[ADDR_WIDTH-1:1], 1'b0}] <= 1'b1;
            erased[{ADDR[ADDR_WIDTH-1:1], 1'b1}] <= 1'b1;
          end
        end
        if (CP_ENABLE && PROG && erased[ADDR]) begin
          if (ADDR < WORDS) begin
            mem[ADDR] <= DIN;
            erased[ADDR] <= 1'b0;
          end
        end
        if (READ) begin
          if (ADDR < WORDS) begin
            DOUT <= mem[ADDR];
          end
          else begin
            DOUT <= 16'hdead;
          end
        end
      end

      if (!IP_EN) begin
        counter <= 32'd0;
        ERASE_last <= 1'b0;
        PROG_last <= 1'b0;
        READ_last <= 1'b0;
        DOUT <= 16'hdead;
        fail <= 1'b0;
      end
    end
  end

  assign READY = IP_EN ? (fail ? 1'b0 : (counter == 16'd0)) : 1'b0;

endmodule


