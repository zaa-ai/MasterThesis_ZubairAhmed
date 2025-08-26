
`timescale 1ns/1ns

// SECDED ECC MODULE

module ecc_6_hd4_shell #(
    parameter DATA_WIDTH = 16,  // without address bits
    parameter ADDR_WIDTH = 0,
    parameter SERIAL     = 0
  )(
    input    [ADDR_WIDTH+DATA_WIDTH-1:0] wdata_bus,  // write data from CPU bus
    output [6+ADDR_WIDTH+DATA_WIDTH-1:0] wdata_mem,  // write data with ECC to memory

    input  [6+ADDR_WIDTH+DATA_WIDTH-1:0] rdata_mem,  // read data with ECC from memory
    output   [ADDR_WIDTH+DATA_WIDTH-1:0] rdata_bus,  // read data to CPU bus

    input                                i_disable,  // disable ECC correction
    output                               corrected,  // single bit error was corrected
    output                               detected    // double bit error was detected
  );

  localparam ECC_BITS = 6;

  wire [ECC_BITS-1:0] ecc_wdata;

  ecc_6_hd4_calc #(
    .DATA_WIDTH (ADDR_WIDTH+DATA_WIDTH),
    .SERIAL     (SERIAL)
  ) ecc_6_hd4_calc_wdata_inst(
    .i_data (wdata_bus),
    .i_ecc  ({ECC_BITS{1'b0}}),
    .o_ecc  (ecc_wdata)
  );

  assign wdata_mem = {ecc_wdata, wdata_bus};

  wire [ECC_BITS-1:0] ecc_rdata;

  ecc_6_hd4_calc #(
    .DATA_WIDTH (ADDR_WIDTH+DATA_WIDTH),
    .SERIAL     (SERIAL)
  ) ecc_6_hd4_calc_rdata_inst(
    .i_data (rdata_mem[0 +: ADDR_WIDTH+DATA_WIDTH]),
    .i_ecc  (rdata_mem[ADDR_WIDTH+DATA_WIDTH +: ECC_BITS]),
    .o_ecc  (ecc_rdata)
  );

  // Only real data bits will be corrected.
  // Any address "bit error" will assert a "detected" (uncorrectable error) event.

  ecc_6_hd4_correct #(
    .DATA_WIDTH (DATA_WIDTH)
  ) ecc_6_hd4_correct_inst(
    .i_ecc       (ecc_rdata),
    .i_data      (rdata_mem[0 +: DATA_WIDTH]),
    .o_data      (rdata_bus[0 +: DATA_WIDTH]),
    .i_disable   (i_disable),
    .o_corrected (corrected),
    .o_detected  (detected)
  );

  generate
    genvar n;
    for (n = 0; n < ADDR_WIDTH; n++) begin : generate_read_data
      assign rdata_bus[DATA_WIDTH+n] = rdata_mem[DATA_WIDTH+n];
    end
  endgenerate

endmodule

