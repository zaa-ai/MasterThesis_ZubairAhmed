
`timescale 1ns/10ps

module ecc_7_hd4_correct #(
    parameter DATA_WIDTH = 32
  )(
    input                 [6:0] i_ecc,
    input      [DATA_WIDTH-1:0] i_data,
    output     [DATA_WIDTH-1:0] o_data,
    input                       i_disable,   // disables the data correction, but not the event signal generation !
    output reg                  o_corrected,
    output reg                  o_detected
  );

  localparam ECC_WIDTH = 7;

  logic [DATA_WIDTH-1:0] data;

  assign o_data = i_disable ? i_data : data;

  logic [ECC_WIDTH-1:0] ecc_syndroms[0:ECC_WIDTH-1];
  // @SuppressProblem -type partially_unread_data -count 1 -length 1
  logic [ECC_WIDTH-1:0] dat_syndroms[0:55];

  // polynomial 0xB7 -> 56 bit with MHD4
  always_comb
  begin
    ecc_syndroms[ 0] = 7'h01;
    ecc_syndroms[ 1] = 7'h02;
    ecc_syndroms[ 2] = 7'h04;
    ecc_syndroms[ 3] = 7'h08;
    ecc_syndroms[ 4] = 7'h10;
    ecc_syndroms[ 5] = 7'h20;
    ecc_syndroms[ 6] = 7'h40;

    dat_syndroms[ 0] = 7'h37;
    dat_syndroms[ 1] = 7'h6e;
    dat_syndroms[ 2] = 7'h6b;
    dat_syndroms[ 3] = 7'h61;
    dat_syndroms[ 4] = 7'h75;
    dat_syndroms[ 5] = 7'h5d;
    dat_syndroms[ 6] = 7'h0d;
    dat_syndroms[ 7] = 7'h1a;
    dat_syndroms[ 8] = 7'h34;
    dat_syndroms[ 9] = 7'h68;

    dat_syndroms[10] = 7'h67;
    dat_syndroms[11] = 7'h79;
    dat_syndroms[12] = 7'h45;
    dat_syndroms[13] = 7'h3d;
    dat_syndroms[14] = 7'h7a;
    dat_syndroms[15] = 7'h43;
    dat_syndroms[16] = 7'h31;
    dat_syndroms[17] = 7'h62;
    dat_syndroms[18] = 7'h73;
    dat_syndroms[19] = 7'h51;

    dat_syndroms[20] = 7'h15;
    dat_syndroms[21] = 7'h2a;
    dat_syndroms[22] = 7'h54;
    dat_syndroms[23] = 7'h1f;
    dat_syndroms[24] = 7'h3e;
    dat_syndroms[25] = 7'h7c;
    dat_syndroms[26] = 7'h4f;
    dat_syndroms[27] = 7'h29;
    dat_syndroms[28] = 7'h52;
    dat_syndroms[29] = 7'h13;

    dat_syndroms[30] = 7'h26;
    dat_syndroms[31] = 7'h4c;
    dat_syndroms[32] = 7'h2f;
    dat_syndroms[33] = 7'h5e;
    dat_syndroms[34] = 7'h0b;
    dat_syndroms[35] = 7'h16;
    dat_syndroms[36] = 7'h2c;
    dat_syndroms[37] = 7'h58;
    dat_syndroms[38] = 7'h07;
    dat_syndroms[39] = 7'h0e;

    dat_syndroms[40] = 7'h1c;
    dat_syndroms[41] = 7'h38;
    dat_syndroms[42] = 7'h70;
    dat_syndroms[43] = 7'h57;
    dat_syndroms[44] = 7'h19;
    dat_syndroms[45] = 7'h32;
    dat_syndroms[46] = 7'h64;
    dat_syndroms[47] = 7'h7f;
    dat_syndroms[48] = 7'h49;
    dat_syndroms[49] = 7'h25;

    dat_syndroms[50] = 7'h4a;
    dat_syndroms[51] = 7'h23;
    dat_syndroms[52] = 7'h46;
    dat_syndroms[53] = 7'h3b;
    dat_syndroms[54] = 7'h76;
    dat_syndroms[55] = 7'h5b;
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

