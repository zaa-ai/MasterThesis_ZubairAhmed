
`timescale 1ns/10ps

module ecc_7_correct(
    input       [6:0] i_ecc,
    input      [31:0] i_data,
    output     [31:0] o_data,
    input             i_disable,
    output reg        o_corrected,
    output reg        o_detected
  );

  logic [31:0] correction;

  assign o_data = i_disable ? i_data : i_data ^ correction;

  // polynom = 0xB7
  always_comb
  begin
      // default -> multibit error detected -> no data correction
                    correction = 32'h0000_0000; o_corrected = 1'b0; o_detected = 1'b1;
    case (i_ecc)
      // correct data -> no correction needed
      7'h00 : begin correction = 32'h0000_0000; o_corrected = 1'b0; o_detected = 1'b0; end

      // single bit errors in data word -> data correction
      7'h37 : begin correction = 32'h0000_0001; o_corrected = 1'b1; o_detected = 1'b0; end
      7'h6e : begin correction = 32'h0000_0002; o_corrected = 1'b1; o_detected = 1'b0; end
      7'h6b : begin correction = 32'h0000_0004; o_corrected = 1'b1; o_detected = 1'b0; end
      7'h61 : begin correction = 32'h0000_0008; o_corrected = 1'b1; o_detected = 1'b0; end
      7'h75 : begin correction = 32'h0000_0010; o_corrected = 1'b1; o_detected = 1'b0; end
      7'h5d : begin correction = 32'h0000_0020; o_corrected = 1'b1; o_detected = 1'b0; end
      7'h0d : begin correction = 32'h0000_0040; o_corrected = 1'b1; o_detected = 1'b0; end
      7'h1a : begin correction = 32'h0000_0080; o_corrected = 1'b1; o_detected = 1'b0; end
      7'h34 : begin correction = 32'h0000_0100; o_corrected = 1'b1; o_detected = 1'b0; end
      7'h68 : begin correction = 32'h0000_0200; o_corrected = 1'b1; o_detected = 1'b0; end
      7'h67 : begin correction = 32'h0000_0400; o_corrected = 1'b1; o_detected = 1'b0; end
      7'h79 : begin correction = 32'h0000_0800; o_corrected = 1'b1; o_detected = 1'b0; end
      7'h45 : begin correction = 32'h0000_1000; o_corrected = 1'b1; o_detected = 1'b0; end
      7'h3d : begin correction = 32'h0000_2000; o_corrected = 1'b1; o_detected = 1'b0; end
      7'h7a : begin correction = 32'h0000_4000; o_corrected = 1'b1; o_detected = 1'b0; end
      7'h43 : begin correction = 32'h0000_8000; o_corrected = 1'b1; o_detected = 1'b0; end
      7'h31 : begin correction = 32'h0001_0000; o_corrected = 1'b1; o_detected = 1'b0; end
      7'h62 : begin correction = 32'h0002_0000; o_corrected = 1'b1; o_detected = 1'b0; end
      7'h73 : begin correction = 32'h0004_0000; o_corrected = 1'b1; o_detected = 1'b0; end
      7'h51 : begin correction = 32'h0008_0000; o_corrected = 1'b1; o_detected = 1'b0; end
      7'h15 : begin correction = 32'h0010_0000; o_corrected = 1'b1; o_detected = 1'b0; end
      7'h2a : begin correction = 32'h0020_0000; o_corrected = 1'b1; o_detected = 1'b0; end
      7'h54 : begin correction = 32'h0040_0000; o_corrected = 1'b1; o_detected = 1'b0; end
      7'h1f : begin correction = 32'h0080_0000; o_corrected = 1'b1; o_detected = 1'b0; end
      7'h3e : begin correction = 32'h0100_0000; o_corrected = 1'b1; o_detected = 1'b0; end
      7'h7c : begin correction = 32'h0200_0000; o_corrected = 1'b1; o_detected = 1'b0; end
      7'h4f : begin correction = 32'h0400_0000; o_corrected = 1'b1; o_detected = 1'b0; end
      7'h29 : begin correction = 32'h0800_0000; o_corrected = 1'b1; o_detected = 1'b0; end
      7'h52 : begin correction = 32'h1000_0000; o_corrected = 1'b1; o_detected = 1'b0; end
      7'h13 : begin correction = 32'h2000_0000; o_corrected = 1'b1; o_detected = 1'b0; end
      7'h26 : begin correction = 32'h4000_0000; o_corrected = 1'b1; o_detected = 1'b0; end
      7'h4c : begin correction = 32'h8000_0000; o_corrected = 1'b1; o_detected = 1'b0; end

      // single bit errors in ecc sum -> no data correction
      7'h01 : begin correction = 32'h0000_0000; o_corrected = 1'b1; o_detected = 1'b0; end
      7'h02 : begin correction = 32'h0000_0000; o_corrected = 1'b1; o_detected = 1'b0; end
      7'h04 : begin correction = 32'h0000_0000; o_corrected = 1'b1; o_detected = 1'b0; end
      7'h08 : begin correction = 32'h0000_0000; o_corrected = 1'b1; o_detected = 1'b0; end
      7'h10 : begin correction = 32'h0000_0000; o_corrected = 1'b1; o_detected = 1'b0; end
      7'h20 : begin correction = 32'h0000_0000; o_corrected = 1'b1; o_detected = 1'b0; end
      7'h40 : begin correction = 32'h0000_0000; o_corrected = 1'b1; o_detected = 1'b0; end
    endcase
  end

endmodule

