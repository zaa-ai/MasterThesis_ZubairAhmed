
`timescale 1ns/1ns

module pure_nand #(
    parameter DOMAIN_3V0 = 0
  )(
    input  i_a,
    input  i_b,
    output o_y
  );

  ND2D2BWP7T nand_inst(
    .A1 (i_a),
    .A2 (i_b),
    .ZN (o_y)
  );

endmodule

