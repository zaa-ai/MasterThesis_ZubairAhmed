
`timescale 1ns/10ps

module pure_ff #(
    parameter DOMAIN_3V0 = 0
  )(
    input         CK,
    input         RN,
    input         D,
    output        Y
  );

  DFCNQD2BWP7T ff_inst(
    .D   (D),
    .CP  (CK),
    .CDN (RN),
    .Q   (Y)
  );

endmodule

