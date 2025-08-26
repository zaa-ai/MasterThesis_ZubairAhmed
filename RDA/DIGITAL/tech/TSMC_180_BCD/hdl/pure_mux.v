
`timescale 1ns/1ns

module pure_mux #(
    parameter DOMAIN_3V0 = 0
  )(
    input  i_a,
    input  i_b,
    input  i_sa,
    output o_y
  );

  MUX2D2BWP7T mux_inst(
    .I0 (i_b),
    .I1 (i_a),
    .S  (i_sa),
    .Z  (o_y)
  );

endmodule

