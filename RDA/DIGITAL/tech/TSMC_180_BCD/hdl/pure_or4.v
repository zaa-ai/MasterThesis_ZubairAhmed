
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

  OR4D2BWP7T or_inst(
    .A1 (i_a),
    .A2 (i_b),
    .A3 (i_c),
    .A4 (i_d),
    .Z  (o_y)
  );

endmodule

