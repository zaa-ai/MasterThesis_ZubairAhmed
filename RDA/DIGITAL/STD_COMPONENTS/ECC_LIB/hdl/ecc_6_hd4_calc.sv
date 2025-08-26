
`timescale 1ns/10ps

module ecc_6_hd4_calc #(
    parameter DATA_WIDTH = 16,
    parameter SERIAL     = 0
  )(
    input  [DATA_WIDTH-1:0] i_data,
    input             [5:0] i_ecc,
    output reg        [5:0] o_ecc
  );

  localparam ECC_BITS = 6;

  generate
    if (SERIAL) begin : serial_ecc_caclulation

      localparam [ECC_BITS:0] POLYNOMIAL = 8'h47;

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
    else begin : parallel_ecc_calculation

      logic [24:0] data;

      always_comb
      begin
        data = '0;
        data[DATA_WIDTH-1:0] = i_data;
      end

      always_comb
      begin
        o_ecc[0] =
          data[ 0] ^ data[ 4] ^ data[ 5] ^ data[ 6] ^ data[ 8] ^ data[10] ^ data[13] ^ 
          data[15] ^ data[16] ^ data[17] ^ data[18] ^ data[21] ^ data[22] ^ data[24] ^ 
          i_ecc[0];

        o_ecc[1] =
          data[ 0] ^ data[ 1] ^ data[ 4] ^ data[ 7] ^ data[ 8] ^ data[ 9] ^ data[10] ^ 
          data[11] ^ data[13] ^ data[14] ^ data[15] ^ data[19] ^ data[21] ^ data[23] ^ 
          data[24] ^ i_ecc[1];

        o_ecc[2] =
          data[ 0] ^ data[ 1] ^ data[ 2] ^ data[ 4] ^ data[ 6] ^ data[ 9] ^ data[11] ^ 
          data[12] ^ data[13] ^ data[14] ^ data[17] ^ data[18] ^ data[20] ^ data[21] ^ 
          i_ecc[2];

        o_ecc[3] =
          data[ 1] ^ data[ 2] ^ data[ 3] ^ data[ 5] ^ data[ 7] ^ data[10] ^ data[12] ^ 
          data[13] ^ data[14] ^ data[15] ^ data[18] ^ data[19] ^ data[21] ^ data[22] ^ 
          i_ecc[3];

        o_ecc[4] =
          data[ 2] ^ data[ 3] ^ data[ 4] ^ data[ 6] ^ data[ 8] ^ data[11] ^ data[13] ^ 
          data[14] ^ data[15] ^ data[16] ^ data[19] ^ data[20] ^ data[22] ^ data[23] ^ 
          i_ecc[4];

        o_ecc[5] =
          data[ 3] ^ data[ 4] ^ data[ 5] ^ data[ 7] ^ data[ 9] ^ data[12] ^ data[14] ^ 
          data[15] ^ data[16] ^ data[17] ^ data[20] ^ data[21] ^ data[23] ^ data[24] ^ 
          i_ecc[5];
      end
    end
  endgenerate

endmodule

