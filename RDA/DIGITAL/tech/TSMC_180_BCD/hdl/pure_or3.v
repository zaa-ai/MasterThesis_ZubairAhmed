
`timescale 1ns/1ns

module pure_or3 #(
    parameter DOMAIN_3V0 = 0
  )(
    input  i_a,
    input  i_b,
    input  i_c,
    output o_y
  );

  OR3D2BWP7T or_inst(
    .A1 (i_a),
    .A2 (i_b),
    .A3 (i_c),
    .Z  (o_y)
  );

endmodule

