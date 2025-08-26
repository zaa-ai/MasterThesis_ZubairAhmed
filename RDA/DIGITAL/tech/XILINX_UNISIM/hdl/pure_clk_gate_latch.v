
`timescale 1ns/1ns

module pure_clk_gate_latch #(
    parameter DOMAIN_3V0 = 0
  )(
    input  in_clk_e,
    input  in_clk,
    output out_clk,
    input  scan_mode
  );

  reg clk_e;

  always @*
  begin
    if (!in_clk) begin
      clk_e = in_clk_e;
    end
  end

  BUFGCE BUFGCE (
    .I  (in_clk),
    .CE (clk_e),
    .O  (out_clk)
  );

endmodule

