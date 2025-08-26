
`timescale 1ns/1ns

module pure_clk_mask #(
    parameter DOMAIN_3V0 = 0
  )(
    input  in_clk,
    input  neg_clk_e,
    output out_clk
  );

  `include "tech.v"

  `ifdef target_technology_FPGA_VIRTEX
    // XILINX VIRTEX variant
    BUFGCE BUFGCE(
      .I  (in_clk),
      .CE (neg_clk_e),
      .O  (out_clk)
    );
  `else
    // XILINX SPARTAN, ARTIX7, KINTEX7 variant
    pure_and pure_and_inst(
      .i_a (in_clk),
      .i_b (neg_clk_e),
      .o_y (out_clk)
    );
  `endif

endmodule

