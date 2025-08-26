
`timescale 1ns/1ns

module pure_mux4 #(
    parameter DOMAIN_3V0 = 0
  )(
    input        i_a0,
    input        i_a1,
    input        i_a2,
    input        i_a3,
    input  [1:0] i_s,
    output       o_y
  );

  MUX4D2BWP7T mux_inst(
    .I0  (i_a0),
    .I1  (i_a1),
    .I2  (i_a2),
    .I3  (i_a3),
    .S0  (i_s[0]),
    .S1  (i_s[1]),
    .Z   (o_y)
  );

endmodule

