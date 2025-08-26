
`timescale 1ns/10ps

module pure_ff #(
    parameter DOMAIN_3V0 = 0
  )(
    input         CK,
//  input         SN,
    input         RN,
    input         D,
    output reg    Y
  );

  always @(posedge CK or negedge RN) // or negedge SN)
  begin
  /* synopsys translate_off */
    #1;
  /* synopsys translate_on */
//  if (!SN) Y <= 1'b1;
    if (!RN) Y <= 1'b0;
    else     Y <= D;
  end

endmodule

