
`timescale 1ns/1ns

module pure_or3 #(
    parameter DOMAIN_3V0 = 0
  )(
    input  i_a,
    input  i_b,
    input  i_c,
    output o_y
  );

  LUT3 #(
    .INIT (8'b1111_1110)
  ) LUT3_inst (
    .I0 (i_a),
    .I1 (i_b),
    .I2 (i_c),
    .O  (o_y)
  ) /* synthesis syn_noprune=1 */ /*synthesis syn_preserve=1 */ ;

endmodule

