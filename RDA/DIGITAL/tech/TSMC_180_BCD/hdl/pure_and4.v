
`timescale 1ns/1ns

module pure_and4 #(
    parameter DOMAIN_3V0 = 0
  )(
    input  i_a,
    input  i_b,
    input  i_c,
    input  i_d,
    output o_y
  );

  AN4D2BWP7T and_inst(
    .A1 (i_a),
    .A2 (i_b),
    .A3 (i_c),
    .A4 (i_d),
    .Z  (o_y)
  );

endmodule

