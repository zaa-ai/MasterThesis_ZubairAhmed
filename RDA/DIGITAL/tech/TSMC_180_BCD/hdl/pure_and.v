
`timescale 1ns/1ns

module pure_and #(
    parameter DOMAIN_3V0 = 0
  )(
    input  i_a,
    input  i_b,
    output o_y
  );

`ifdef POST_LAYOUT  // zero-delay when used in post-layout TB code
  assign o_y = i_a & i_b;
`else
  AN2D2BWP7T and_inst(
    .A1 (i_a),
    .A2 (i_b),
    .Z (o_y)
  );
`endif

endmodule

