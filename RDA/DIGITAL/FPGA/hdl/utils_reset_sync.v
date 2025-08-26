
`timescale 1ns/10ps

module utils_reset_sync #(
    parameter DOMAIN_3V0 = 0,
    parameter LENGTH     = 2     // >= 2
  ) (
    input         clk,

    input         i_nrst,
    output        o_nrst,

    input         i_scan_mode
  );

  reg [LENGTH-1:0] nrst_sync;

  always @(negedge i_nrst or posedge clk)
  begin
    if (!i_nrst) begin
      nrst_sync <= {LENGTH{1'b0}};
    end
    else begin
      nrst_sync <= {nrst_sync[LENGTH-2:0], 1'b1};
    end
  end

  pure_mux #(.DOMAIN_3V0(DOMAIN_3V0)) pure_mux_inst(
    .i_a  (i_nrst),
    .i_b  (nrst_sync[LENGTH-1]),
    .i_sa (i_scan_mode),
    .o_y  (o_nrst)
  );

endmodule

