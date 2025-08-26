
`timescale 1ns/1ns

module pure_delay #(
    parameter DOMAIN_3V0 = 0
  )(
    input  i_a,
    output o_y
  );

  assign o_y = i_a;

endmodule

