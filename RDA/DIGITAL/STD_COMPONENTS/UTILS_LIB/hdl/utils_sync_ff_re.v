`timescale 1ns/1ns

module utils_sync_ff_re #(
    parameter DEFAULT_VAL = 1'b0
  )(
    input      rn,
    input      ck,
    input      d,
    output reg q
  );

  always @(negedge rn or posedge ck)
  begin
    if (!rn) begin
      q <= DEFAULT_VAL;
    end
    else begin
      q <= d;
    end
  end

endmodule

