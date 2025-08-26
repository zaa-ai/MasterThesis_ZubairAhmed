
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

  wire a01, a23;

  pure_mux pure_mux_a01_inst(.i_a(i_a1), .i_b(i_a0), .i_sa(i_s[0]), .o_y(a01));
  pure_mux pure_mux_a23_inst(.i_a(i_a3), .i_b(i_a2), .i_sa(i_s[0]), .o_y(a23));
  pure_mux pure_mux_out_inst(.i_a(a23),  .i_b(a01),  .i_sa(i_s[1]), .o_y(o_y));

endmodule

