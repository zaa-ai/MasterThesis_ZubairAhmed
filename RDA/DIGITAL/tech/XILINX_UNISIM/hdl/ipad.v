
`timescale 1ns/1ns

module ipad(
    output  C,
    input   PAD
  );

  IBUF IBUF_inst(
    .I (PAD),
    .O (C)
  );

endmodule

