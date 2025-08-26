
`timescale 1ns/1ns

module pure_inv #(
    parameter DOMAIN_3V0 = 0
  )(
    input  i_a,
    output o_y
  );

  INVD2BWP7T inv_inst(
    .I  (i_a),
    .ZN (o_y)
  );

endmodule

