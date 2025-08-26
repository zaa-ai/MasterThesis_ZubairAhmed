
module sync_sram #(
		parameter NUM_PARTS  = 2,
		parameter DATA_WIDTH = 16,
		parameter ADDR_WIDTH = 10,
		parameter DEPTH      = 1024
		)(
		input                           clk,    // clk
		input                           nrst,   // nreset

		input                           ce,     // chip enable
		input           [NUM_PARTS-1:0] we,     // part write enable
		input           [NUM_PARTS-1:0] oe,     // part output enable
		input          [ADDR_WIDTH-1:0] addr,   // address
		input          [DATA_WIDTH-1:0] wdata,  // data in
		output         [DATA_WIDTH-1:0] rdata   // ram out
		);

	sram_3072x23 sram_inst (
			.clka  (~clk),
			.wea   (we),
			.addra (addr),
			.dina  (wdata),
			.douta (rdata)
		);

	//	sync_sram_slice #(
	//		.DATA_WIDTH (DATA_WIDTH/NUM_PARTS),
	//		.DEPTH      (DEPTH)
	//	) sync_sram_slice_inst[NUM_PARTS-1:0](
	//		.clk   (clk),
	//		.ce    (ce),
	//		.we    (we),
	//		.addr  (addr),
	//		.wdata (wdata),
	//		.rdata (rdata)
	//	);

endmodule

