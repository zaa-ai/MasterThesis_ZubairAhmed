
`timescale 1ns/1ns

module pure_inv #(
    parameter DOMAIN_3V0 = 0
  )(
    input  i_a,
    output o_y
  );

  LUT1 #(
    .INIT (2'b01)
  ) LUT1_inst (
    .I0 (i_a),
    .O  (o_y)
  ) /* synthesis syn_noprune=1 */ /*synthesis syn_preserve=1 */ ;

endmodule

