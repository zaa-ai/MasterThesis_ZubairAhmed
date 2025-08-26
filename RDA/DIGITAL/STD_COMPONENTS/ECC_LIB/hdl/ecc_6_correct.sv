
`timescale 1ns/10ps

module ecc_6_correct(
    input       [5:0] i_ecc,
    input      [15:0] i_data,
    output     [15:0] o_data,
    input             i_disable,
    output reg        o_corrected,
    output reg        o_detected
  );

  logic [15:0] correction;

  assign o_data = i_disable ? i_data : i_data ^ correction;

  // polynom = 0x5F
  always_comb
  begin
      // default -> multibit error detected -> no data correction
                    correction = 16'h0000; o_corrected = 1'b0; o_detected = 1'b1;
    case (i_ecc)
      // correct data -> no correction needed
      6'h00 : begin correction = 16'h0000; o_corrected = 1'b0; o_detected = 1'b0; end

      // single bit errors in data word -> data correction
      6'h1F : begin correction = 16'h0001; o_corrected = 1'b1; o_detected = 1'b0; end
      6'h3E : begin correction = 16'h0002; o_corrected = 1'b1; o_detected = 1'b0; end
      6'h23 : begin correction = 16'h0004; o_corrected = 1'b1; o_detected = 1'b0; end
      6'h19 : begin correction = 16'h0008; o_corrected = 1'b1; o_detected = 1'b0; end
      6'h32 : begin correction = 16'h0010; o_corrected = 1'b1; o_detected = 1'b0; end
      6'h3b : begin correction = 16'h0020; o_corrected = 1'b1; o_detected = 1'b0; end
      6'h29 : begin correction = 16'h0040; o_corrected = 1'b1; o_detected = 1'b0; end
      6'h0d : begin correction = 16'h0080; o_corrected = 1'b1; o_detected = 1'b0; end
      6'h1a : begin correction = 16'h0100; o_corrected = 1'b1; o_detected = 1'b0; end
      6'h34 : begin correction = 16'h0200; o_corrected = 1'b1; o_detected = 1'b0; end
      6'h37 : begin correction = 16'h0400; o_corrected = 1'b1; o_detected = 1'b0; end
      6'h31 : begin correction = 16'h0800; o_corrected = 1'b1; o_detected = 1'b0; end
      6'h3d : begin correction = 16'h1000; o_corrected = 1'b1; o_detected = 1'b0; end
      6'h25 : begin correction = 16'h2000; o_corrected = 1'b1; o_detected = 1'b0; end
      6'h15 : begin correction = 16'h4000; o_corrected = 1'b1; o_detected = 1'b0; end
      6'h2a : begin correction = 16'h8000; o_corrected = 1'b1; o_detected = 1'b0; end

      // single bit errors in ecc sum -> no data correction
      6'h01 : begin correction = 16'h0000; o_corrected = 1'b1; o_detected = 1'b0; end
      6'h02 : begin correction = 16'h0000; o_corrected = 1'b1; o_detected = 1'b0; end
      6'h04 : begin correction = 16'h0000; o_corrected = 1'b1; o_detected = 1'b0; end
      6'h08 : begin correction = 16'h0000; o_corrected = 1'b1; o_detected = 1'b0; end
      6'h10 : begin correction = 16'h0000; o_corrected = 1'b1; o_detected = 1'b0; end
      6'h20 : begin correction = 16'h0000; o_corrected = 1'b1; o_detected = 1'b0; end
    endcase
  end

endmodule

