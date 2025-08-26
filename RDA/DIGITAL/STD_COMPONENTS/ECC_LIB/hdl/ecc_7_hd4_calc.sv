
`timescale 1ns/10ps

module ecc_7_hd4_calc #(
    parameter DATA_WIDTH = 32,
    parameter SERIAL     = 0
  )(
    input  [DATA_WIDTH-1:0] i_data,
    input             [6:0] i_ecc,
    output reg        [6:0] o_ecc
  );

  localparam ECC_BITS = 7;

  generate
    if (SERIAL) begin : serial_calculation

      localparam [ECC_BITS:0] POLYNOMIAL = 8'hB7;

      logic [(DATA_WIDTH+ECC_BITS)-1:0] shiftreg;

      integer b;

      always_comb
      begin
        shiftreg = {i_data, i_ecc};

        for (b = 0; b < DATA_WIDTH; b++) begin
          if (shiftreg[DATA_WIDTH+ECC_BITS-1]) begin
            shiftreg = shiftreg ^ {POLYNOMIAL, {DATA_WIDTH-1{1'b0}}};
          end
          shiftreg = shiftreg << 1;
        end
        o_ecc = shiftreg[DATA_WIDTH +: ECC_BITS];
      end

    end
    else begin : parallel_calculation

      logic [55:0] data;

      always_comb
      begin
        data = '0;
        data[DATA_WIDTH-1:0] = i_data;
      end

      always_comb
      begin
        o_ecc[0] =
          data[ 0] ^ data[ 2] ^ data[ 3] ^ data[ 4] ^ data[ 5] ^ data[ 6] ^ data[10] ^ 
          data[11] ^ data[12] ^ data[13] ^ data[15] ^ data[16] ^ data[18] ^ data[19] ^ 
          data[20] ^ data[23] ^ data[26] ^ data[27] ^ data[29] ^ data[32] ^ data[34] ^ 
          data[38] ^ data[43] ^ data[44] ^ data[47] ^ data[48] ^ data[49] ^ data[51] ^ 
          data[53] ^ data[55] ^ i_ecc[0];

        o_ecc[1] =
          data[ 0] ^ data[ 1] ^ data[ 2] ^ data[ 7] ^ data[10] ^ data[14] ^ data[15] ^ 
          data[17] ^ data[18] ^ data[21] ^ data[23] ^ data[24] ^ data[26] ^ data[28] ^ 
          data[29] ^ data[30] ^ data[32] ^ data[33] ^ data[34] ^ data[35] ^ data[38] ^ 
          data[39] ^ data[43] ^ data[45] ^ data[47] ^ data[50] ^ data[51] ^ data[52] ^ 
          data[53] ^ data[54] ^ data[55] ^ i_ecc[1];

        o_ecc[2] =
          data[ 0] ^ data[ 1] ^ data[ 4] ^ data[ 5] ^ data[ 6] ^ data[ 8] ^ data[10] ^ 
          data[12] ^ data[13] ^ data[20] ^ data[22] ^ data[23] ^ data[24] ^ data[25] ^ 
          data[26] ^ data[30] ^ data[31] ^ data[32] ^ data[33] ^ data[35] ^ data[36] ^ 
          data[38] ^ data[39] ^ data[40] ^ data[43] ^ data[46] ^ data[47] ^ data[49] ^ 
          data[52] ^ data[54] ^ i_ecc[2];

        o_ecc[3] =
          data[ 1] ^ data[ 2] ^ data[ 5] ^ data[ 6] ^ data[ 7] ^ data[ 9] ^ data[11] ^ 
          data[13] ^ data[14] ^ data[21] ^ data[23] ^ data[24] ^ data[25] ^ data[26] ^ 
          data[27] ^ data[31] ^ data[32] ^ data[33] ^ data[34] ^ data[36] ^ data[37] ^ 
          data[39] ^ data[40] ^ data[41] ^ data[44] ^ data[47] ^ data[48] ^ data[50] ^ 
          data[53] ^ data[55] ^ i_ecc[3];

        o_ecc[4] =
          data[ 0] ^ data[ 4] ^ data[ 5] ^ data[ 7] ^ data[ 8] ^ data[11] ^ data[13] ^ 
          data[14] ^ data[16] ^ data[18] ^ data[19] ^ data[20] ^ data[22] ^ data[23] ^ 
          data[24] ^ data[25] ^ data[28] ^ data[29] ^ data[33] ^ data[35] ^ data[37] ^ 
          data[40] ^ data[41] ^ data[42] ^ data[43] ^ data[44] ^ data[45] ^ data[47] ^ 
          data[53] ^ data[54] ^ data[55] ^ i_ecc[4];

        o_ecc[5] =
          data[ 0] ^ data[ 1] ^ data[ 2] ^ data[ 3] ^ data[ 4] ^ data[ 8] ^ data[ 9] ^ 
          data[10] ^ data[11] ^ data[13] ^ data[14] ^ data[16] ^ data[17] ^ data[18] ^ 
          data[21] ^ data[24] ^ data[25] ^ data[27] ^ data[30] ^ data[32] ^ data[36] ^ 
          data[41] ^ data[42] ^ data[45] ^ data[46] ^ data[47] ^ data[49] ^ data[51] ^ 
          data[53] ^ data[54] ^ i_ecc[5];

        o_ecc[6] =
          data[ 1] ^ data[ 2] ^ data[ 3] ^ data[ 4] ^ data[ 5] ^ data[ 9] ^ data[10] ^ 
          data[11] ^ data[12] ^ data[14] ^ data[15] ^ data[17] ^ data[18] ^ data[19] ^ 
          data[22] ^ data[25] ^ data[26] ^ data[28] ^ data[31] ^ data[33] ^ data[37] ^ 
          data[42] ^ data[43] ^ data[46] ^ data[47] ^ data[48] ^ data[50] ^ data[52] ^ 
          data[54] ^ data[55] ^ i_ecc[6];
      end
    end
  endgenerate

endmodule

