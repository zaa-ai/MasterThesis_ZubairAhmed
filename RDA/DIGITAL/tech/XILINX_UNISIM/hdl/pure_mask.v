
`timescale 1ns/1ns

module pure_mask #(
    parameter MASK_TO    = 0,
    parameter INVERT_M   = 0,
    parameter DOMAIN_3V0 = 0
  )(
    input  i_a,
    input  i_m,
    output o_y
  );

  wire m_or;
  wire m_and;

  generate
    if (INVERT_M) begin

      if (MASK_TO) begin
        pure_inv pure_inv_inst(
          .i_a (i_m),
          .o_y (m_or)
        );
      end
      assign m_and = i_m;

    end
    else begin

      assign m_or = i_m;
      if (!MASK_TO) begin
        pure_inv pure_inv_inst(
          .i_a (i_m),
          .o_y (m_and)
        );
      end

    end
  endgenerate

  generate
    if (MASK_TO) begin

      pure_or pure_or_inst(
        .i_a (i_a),
        .i_b (m_or),
        .o_y (o_y)
      );

    end
    else begin

      pure_and pure_and_inst(
        .i_a (i_a),
        .i_b (m_and),
        .o_y (o_y)
      );

    end
  endgenerate

endmodule

