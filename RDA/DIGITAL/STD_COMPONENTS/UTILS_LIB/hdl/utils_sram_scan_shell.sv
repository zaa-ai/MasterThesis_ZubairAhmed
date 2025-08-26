
`timescale 1ns/10ps

module utils_sram_scan_shell #(
		parameter NUM_PARTS  = 2,
		parameter DATA_WIDTH = 16,
		parameter ADDR_WIDTH = 10,
		parameter DEPTH      = 1024
		)(
		input                           clk,
		input                           nrst,

		input                           ce,     // chip enable
		input           [NUM_PARTS-1:0] we,     // part write enable
		input           [NUM_PARTS-1:0] oe,     // part output enable
		input          [ADDR_WIDTH-1:0] addr,   // address
		input          [DATA_WIDTH-1:0] wdata,  // data in
		output         [DATA_WIDTH-1:0] rdata,  // data out

		input                           scan_mode
		);

	`include "vlog_functions_inc.sv"

	//	localparam ADDR_WIDTH = num2width(DEPTH-1);

	// quiet SRAM input signals to save power ...

	wire  [NUM_PARTS-1:0] we_quiet;
	wire  [NUM_PARTS-1:0] oe_quiet;
	wire [ADDR_WIDTH-1:0] addr_quiet;

	pure_and pure_and_quiet_control_inst[ADDR_WIDTH+2*NUM_PARTS-1:0](
			.i_a ({
					addr,
					oe,
					we
				}),
			.i_b (ce),
			.o_y ({
					addr_quiet,
					oe_quiet,
					we_quiet
				})
		);

	wire [DATA_WIDTH-1:0] wdata_quiet;

	generate
		genvar p;
		for (p = 0; p < NUM_PARTS; p = p + 1) begin : quiet_wdata_inst

			pure_and pure_and_quiet_wdata_inst[DATA_WIDTH/NUM_PARTS-1:0](
					.i_a (wdata[p*DATA_WIDTH/NUM_PARTS +: DATA_WIDTH/NUM_PARTS]),
					.i_b ({DATA_WIDTH/NUM_PARTS{we_quiet[p]}}),
					.o_y (wdata_quiet[p*DATA_WIDTH/NUM_PARTS +: DATA_WIDTH/NUM_PARTS])
				);

		end
	endgenerate

	// delay output enable by one clock cycle ...

	reg [NUM_PARTS-1:0] oe_sync;
	// DMOS: due to one cycle accesses we can't delay output enable by one clock cycle
	//
	//	always @(negedge nrst or posedge clk)
	//	begin
	//		if (!nrst) begin
	//			oe_sync <= {NUM_PARTS{1'b0}};
	//		end
	//		else begin
	//			oe_sync <= ce ? oe_quiet : {NUM_PARTS{1'b0}};
	//		end
	//	end

	assign oe_sync = ce ? oe_quiet : {NUM_PARTS{1'b0}};

	// SRAM input signals are not mask during SCAN -> SCAN may write RAM
	// SRAM output data is masked during SCAN -> prevent undefined data
	// some SRAM control signals are masked to force SRAM standby mode (IDDQ)

	wire                  ce_scan;
	wire  [NUM_PARTS-1:0] oe_scan;

	pure_and pure_and_pre_ram_scan_inst[NUM_PARTS:0](
			.i_a (~scan_mode),
			.i_b ({
					ce,
					oe_sync
				}),
			.o_y ({
					ce_scan,
					oe_scan
				})
		);

	// technology dependent SRAM instance ...

	wire [DATA_WIDTH-1:0] rdata_raw;

	sync_sram #(
			.NUM_PARTS  (NUM_PARTS),
			.DATA_WIDTH (DATA_WIDTH),
			.ADDR_WIDTH (ADDR_WIDTH),
			.DEPTH      (DEPTH)
		) sync_sram_inst(
			.clk   (clk),
			.ce    (ce_scan),
			.we    (we_quiet),
			.oe    (oe_scan),
			.addr  (addr_quiet),
			.wdata (wdata_quiet),
			.rdata (rdata_raw)
		);

	// possible floating read data output masks ...

	wire [DATA_WIDTH-1:0] rdata_non_scan;

	generate
		genvar r;
		for (r = 0; r < NUM_PARTS; r = r + 1) begin : pure_and_data 

			pure_and pure_and_inst[DATA_WIDTH/NUM_PARTS-1:0](
					.i_a (rdata_raw[r*DATA_WIDTH/NUM_PARTS +: DATA_WIDTH/NUM_PARTS]),
					.i_b ({DATA_WIDTH/NUM_PARTS{oe_scan[r]}}),
					.o_y (rdata_non_scan[r*DATA_WIDTH/NUM_PARTS +: DATA_WIDTH/NUM_PARTS])
				);

		end
	endgenerate

	reg [DATA_WIDTH-1:0] rdata_scan;

	always_ff @(negedge nrst or posedge clk) begin
		if (!nrst) begin
			rdata_scan <= '0;
		end
		else begin
			if (scan_mode == 1'b1) 
				rdata_scan <= wdata_quiet ^ addr_quiet ^ {oe_scan, ce_scan, ce, oe_sync, we_quiet} ^ rdata_non_scan;
		end
	end

	pure_mux pure_mux_post_ram_scan_inst[DATA_WIDTH-1:0](
			.i_a  (rdata_scan),
			.i_b  (rdata_non_scan),
			.i_sa (scan_mode),
			.o_y  (rdata)
		);

endmodule

