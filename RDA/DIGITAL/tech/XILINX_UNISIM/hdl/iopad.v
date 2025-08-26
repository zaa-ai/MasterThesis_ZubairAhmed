
`timescale 1ns/1ns

module iopad(
    input   I,
    input   IE,
    input   OEN,
    output  C,
    inout   PAD
  );

  wire in;

  IOBUF IOBUF_inst(
    .IO (PAD),
    .I  (I),
    .T  (OEN),  // (T=1 -> IO=Z)
    .O  (in)
  );

  assign C = in & IE;

endmodule

