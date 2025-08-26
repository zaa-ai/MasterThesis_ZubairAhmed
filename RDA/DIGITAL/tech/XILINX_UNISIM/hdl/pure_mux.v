
`timescale 1ns/1ns

module pure_mux #(
    parameter DOMAIN_3V0 = 0
  )(
    input  i_a,
    input  i_b,
    input  i_sa,
    output o_y
  );

  LUT3 #(
    .INIT (8'b1010_1100)
  ) LUT3_inst (
    .I0 (i_a),
    .I1 (i_b),
    .I2 (i_sa),
    .O  (o_y)
  ) /* synthesis syn_noprune=1 */ /*synthesis syn_preserve=1 */ ;

endmodule

