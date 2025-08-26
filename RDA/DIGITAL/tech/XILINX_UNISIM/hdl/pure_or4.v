
`timescale 1ns/1ns

module pure_or4 #(
    parameter DOMAIN_3V0 = 0
  )(
    input  i_a,
    input  i_b,
    input  i_c,
    input  i_d,
    output o_y
  );

  LUT4 #(
    .INIT (16'b1111_1111_1111_1110)
  ) LUT4_inst (
    .I0 (i_a),
    .I1 (i_b),
    .I2 (i_c),
    .I3 (i_d),
    .O  (o_y)
  ) /* synthesis syn_noprune=1 */ /*synthesis syn_preserve=1 */ ;

endmodule

