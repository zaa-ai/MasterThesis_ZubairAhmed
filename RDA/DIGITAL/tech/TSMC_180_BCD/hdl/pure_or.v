
`timescale 1ns/1ns

module pure_or #(
    parameter DOMAIN_3V0 = 0
  )(
    input  i_a,
    input  i_b,
    output o_y
  );

  OR2D2BWP7T or_inst(
    .A1 (i_a),
    .A2 (i_b),
    .Z  (o_y)
  );

endmodule

