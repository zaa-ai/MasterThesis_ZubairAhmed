
`timescale 1ns/10ps

module ecc_6_hd4_correct #(
    parameter DATA_WIDTH = 16
  )(
    input                 [5:0] i_ecc,
    input      [DATA_WIDTH-1:0] i_data,
    output     [DATA_WIDTH-1:0] o_data,
    input                       i_disable,   // disables the data correction, but not the event signal generation !
    output reg                  o_corrected,
    output reg                  o_detected
  );

  localparam ECC_WIDTH = 6;

  logic [DATA_WIDTH-1:0] data;

  assign o_data = i_disable ? i_data : data;

  logic [ECC_WIDTH-1:0] ecc_syndroms[0:ECC_WIDTH-1];
  logic [ECC_WIDTH-1:0] dat_syndroms[0:24];

  // polynomial 0x47 -> 25 bit with MHD4
  always_comb
  begin
    ecc_syndroms[ 0] = 6'h01;
    ecc_syndroms[ 1] = 6'h02;
    ecc_syndroms[ 2] = 6'h04;
    ecc_syndroms[ 3] = 6'h08;
    ecc_syndroms[ 4] = 6'h10;
    ecc_syndroms[ 5] = 6'h20;

    dat_syndroms[ 0] = 6'h07;
    dat_syndroms[ 1] = 6'h0e;
    dat_syndroms[ 2] = 6'h1c;
    dat_syndroms[ 3] = 6'h38;
    dat_syndroms[ 4] = 6'h37;
    dat_syndroms[ 5] = 6'h29;
    dat_syndroms[ 6] = 6'h15;
    dat_syndroms[ 7] = 6'h2a;
    dat_syndroms[ 8] = 6'h13;
    dat_syndroms[ 9] = 6'h26;

    dat_syndroms[10] = 6'h0b;
    dat_syndroms[11] = 6'h16;
    dat_syndroms[12] = 6'h2c;
    dat_syndroms[13] = 6'h1f;
    dat_syndroms[14] = 6'h3e;
    dat_syndroms[15] = 6'h3b;
    dat_syndroms[16] = 6'h31;
    dat_syndroms[17] = 6'h25;
    dat_syndroms[18] = 6'h0d;
    dat_syndroms[19] = 6'h1a;

    dat_syndroms[20] = 6'h34;
    dat_syndroms[21] = 6'h2f;
    dat_syndroms[22] = 6'h19;
    dat_syndroms[23] = 6'h32;
    dat_syndroms[24] = 6'h23;
  end

  integer n;

  always_comb
  begin
    // default -> multi-bit error detected -> no data correction, but detected event
    o_corrected = 1'b0;
    o_detected = 1'b1;
    data = i_data;

    // correct data -> no correction needed
    if (!i_ecc) begin
      o_corrected = 1'b0;
      o_detected = 1'b0;
    end

    // single bit errors in ecc sum -> no data correction
    for (n = 0; n < ECC_WIDTH; n++) begin
      if (i_ecc == ecc_syndroms[n]) begin
        o_corrected = 1'b1;
        o_detected = 1'b0;
      end
    end

    // single bit errors in data word -> data correction
    for (n = 0; n < DATA_WIDTH; n++) begin
      if (i_ecc == dat_syndroms[n]) begin
        o_corrected = 1'b1;
        o_detected = 1'b0;
        data[n] = ~i_data[n];
      end
    end
  end

endmodule

