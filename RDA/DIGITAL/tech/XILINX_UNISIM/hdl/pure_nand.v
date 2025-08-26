
`timescale 1ns/1ns

module pure_nand #(
    parameter DOMAIN_3V0 = 0
  )(
    input  i_a,
    input  i_b,
    output o_y
  );

  LUT2 #(
    .INIT (4'b0111)
  ) LUT2_inst (
    .I0 (i_a),
    .I1 (i_b),
    .O  (o_y)
  ) /* synthesis syn_noprune=1 */ /*synthesis syn_preserve=1 */ ;

endmodule

