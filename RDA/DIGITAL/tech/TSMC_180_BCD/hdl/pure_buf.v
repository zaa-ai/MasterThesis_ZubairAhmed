
`timescale 1ns/1ns

module pure_buf #(
    parameter DOMAIN_3V0 = 0
  )(
    input  i_a,
    output o_y
  );

  BUFFD2BWP7T buf_inst(
    .I (i_a),
    .Z (o_y)
  );

endmodule

