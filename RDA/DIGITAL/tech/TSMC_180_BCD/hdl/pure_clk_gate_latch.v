
`timescale 1ns/1ns

module pure_clk_gate_latch #(
    parameter DOMAIN_3V0 = 0
  )(
    input  in_clk_e,
    input  in_clk,
    output out_clk,
    input  scan_mode
  );

  CKLNQD2BWP7T gate_inst(
    .CP   (in_clk),
    .E    (in_clk_e),
    .TE   (scan_mode),
    .Q    (out_clk)
  );

endmodule

