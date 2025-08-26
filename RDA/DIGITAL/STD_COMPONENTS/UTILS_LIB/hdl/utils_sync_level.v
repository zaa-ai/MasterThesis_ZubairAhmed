
`timescale 1ns/1ns

module utils_sync_level #(
    parameter DEFAULT_VAL = 1'b0
  )(
    // input domain
    input      in_val,
    // output domain
    input      out_clk,
    input      out_nres,
    output     out_val
  );

  wire s_val_0;

  utils_sync_ff_re #(.DEFAULT_VAL(DEFAULT_VAL)) i_utils_sync_ff_re(
    .rn(out_nres),
    .ck(out_clk),
    .d (in_val),
    .q (s_val_0)
  );

  utils_ff_re #(.DEFAULT_VAL(DEFAULT_VAL)) i_utils_ff_re(
    .rn(out_nres),
    .ck(out_clk),
    .d (s_val_0),
    .q (out_val)
  );

endmodule

