
`timescale 1ns/1ns

module opad(
    input   I,
    output  PAD
  );

  OBUF OBUF_inst(
    .I (I),
    .O (PAD)
  );

endmodule

