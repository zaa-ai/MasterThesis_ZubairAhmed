
`timescale 1ns/10ps

module utils_sram_with_bist #(
		parameter NUM_PARTS    = 2,
		parameter DATA_WIDTH   = 16,
		parameter ADDR_WIDTH   = 10,
		parameter DEPTH        = 1024,
		parameter WITH_PARITY  = 1,
		parameter WITH_ECC     = 0,
		parameter PROTECT_ADDR = 0,
		parameter MARCH_17N    = 0
	)(
		input                           clk,
		input                           nrst,

		output                          parity_event,
		output logic                    corrected,

		bist_if.sp                      bist,

		input                           ce,    // chip enable
		input           [NUM_PARTS-1:0] we,    // part write enable
		input           [NUM_PARTS-1:0] oe,    // part output enable
		//		input  [num2width(DEPTH-1)-1:0] addr,  // address
		input          [ADDR_WIDTH-1:0] addr,  // address
		input          [DATA_WIDTH-1:0] wdata, // data in
		output         [DATA_WIDTH-1:0] rdata, // data out

		input                           scan_mode
	);

	import bist_pkg::*;

	`include "vlog_functions_inc.sv"

	//	localparam ADDR_WIDTH = num2width(DEPTH-1);
	localparam PART_WIDTH = DATA_WIDTH / NUM_PARTS;

	localparam BITS_TO_PROTECT = PROTECT_ADDR ? (PART_WIDTH + ADDR_WIDTH) : PART_WIDTH;

	localparam PART_ECC_BITS = (BITS_TO_PROTECT > 25) ? 7 :
		(BITS_TO_PROTECT > 10) ? 6 : 5;

	localparam PART_PAR_BITS = PROTECT_ADDR ? 2 : 1;

	localparam SRAM_DATA_WIDTH = WITH_ECC    ? (DATA_WIDTH + PART_ECC_BITS * NUM_PARTS) :
		WITH_PARITY ? (DATA_WIDTH + PART_PAR_BITS * NUM_PARTS) : DATA_WIDTH;

	//========================================================================
	// SRAM initialization at startup
	//========================================================================

	wire                          ce_zero;
	wire          [NUM_PARTS-1:0] we_zero;
	wire          [NUM_PARTS-1:0] oe_zero;
	wire [num2width(DEPTH-1)-1:0] addr_zero;
	wire    	 [DATA_WIDTH-1:0] wdata_zero;
	
	assign ce_zero = 1'b0;
	assign we_zero = '0;
	assign oe_zero = '0;
	assign addr_zero = '0;
	assign wdata_zero = '0;
	
	wire zero_busy;
	assign zero_busy = 1'b0;

	wire                          ce_mux    = zero_busy ? ce_zero    : ce;
	wire          [NUM_PARTS-1:0] we_mux    = zero_busy ? we_zero    : we;
	wire          [NUM_PARTS-1:0] oe_mux    = zero_busy ? oe_zero    : oe;
	wire [num2width(DEPTH-1)-1:0] addr_mux  = zero_busy ? addr_zero  : addr;
	wire         [DATA_WIDTH-1:0] wdata_mux = zero_busy ? wdata_zero : wdata;
	wire         [DATA_WIDTH-1:0] rdata_mux;

	assign rdata = rdata_mux;

	//========================================================================

	logic parity_swap;

	utils_sync_level utils_sync_level_parity_swap_inst(
			.in_val   (bist.parity_swap),
			.out_clk  (clk),
			.out_nres (nrst),
			.out_val  (parity_swap)
		);

	wire [NUM_PARTS-1:0] parity_events;

	assign parity_event = |parity_events;

	//========================================================================
	// SRAM ECC/parity instance
	//========================================================================

	wire [SRAM_DATA_WIDTH-1:0] wdata_extended;
	wire [SRAM_DATA_WIDTH-1:0] rdata_extended;

	generate
		if (WITH_ECC) begin : generate_ram_with_ecc

			wire                     ecc_sel;

			utils_sync_level utils_sync_level_ecc_sel_val_inst(
					.in_val   ({bist.ecc_sel}),
					.out_clk  (clk),
					.out_nres (nrst),
					.out_val  (ecc_sel)
				);

			utils_sram_ecc #(
					.ADDR_WIDTH    (ADDR_WIDTH),
					.PART_WIDTH    (PART_WIDTH),
					.PART_ECC_BITS (PART_ECC_BITS),
					.PROTECT_ADDR  (PROTECT_ADDR)
				) utils_sram_ecc_inst[NUM_PARTS-1:0](
					.clk          (clk),
					.nrst         (nrst),

					.parity_swap  (parity_swap),
					.parity_event (parity_events),
					.corrected_event (corrected),
					.ecc_val      (bist.ecc_val[PART_ECC_BITS-1:0]),
					.ecc_sel      (ecc_sel),

					.ce           (ce_mux),
					.oe           (oe_mux),
					.addr         (addr_mux),
					.wdata        (wdata_mux),
					.rdata        (rdata_mux),

					.wdata_sram   (wdata_extended),
					.rdata_sram   (rdata_extended)
				);

		end
		else if (WITH_PARITY) begin : generate_ram_with_parity

			wire [PART_PAR_BITS-1:0] par_val;
			wire                     par_sel;

			utils_sync_level utils_sync_level_ecc_sel_val_inst[1+PART_PAR_BITS-1:0](
					.in_val   ({bist.ecc_sel, bist.ecc_val[PART_PAR_BITS-1:0]}),
					.out_clk  (clk),
					.out_nres (nrst),
					.out_val  ({par_sel, par_val})
				);

			utils_sram_parity #(
					.ADDR_WIDTH    (ADDR_WIDTH),
					.PART_WIDTH    (PART_WIDTH),
					.PART_PAR_BITS (PART_PAR_BITS),
					.PROTECT_ADDR  (PROTECT_ADDR)
				) utils_sram_parity_inst[NUM_PARTS-1:0](
					.clk          (clk),
					.nrst         (nrst),

					.parity_swap  (parity_swap),
					.parity_event (parity_events),
					.par_val      (par_val),
					.par_sel      (par_sel),

					.ce           (ce_mux),
					.oe           (oe_mux),
					.addr         (addr_mux),
					.wdata        (wdata_mux),
					.rdata        (rdata_mux),

					.wdata_sram   (wdata_extended),
					.rdata_sram   (rdata_extended)
				);

		end
		else begin : generate_ram

			assign parity_events = '0;
			assign wdata_extended = wdata_mux;
			assign rdata_mux = rdata_extended;

		end
	endgenerate

	//========================================================================
	// SRAM bist instance
	//========================================================================

	logic bist_run_sync;

	wire                          ce_bist;
	wire          [NUM_PARTS-1:0] we_bist;
	wire          [NUM_PARTS-1:0] oe_bist;
	//	wire [num2width(DEPTH-1)-1:0] addr_bist;
	wire         [ADDR_WIDTH-1:0] addr_bist;
	wire    [SRAM_DATA_WIDTH-1:0] wdata_bist;
	wire    [SRAM_DATA_WIDTH-1:0] rdata_bist;

	utils_sram_bist #(
			.NUM_PARTS    (NUM_PARTS),
			.DATA_WIDTH   (SRAM_DATA_WIDTH),
			.ADDR_WIDTH   (ADDR_WIDTH),
			.DEPTH        (DEPTH),
			.MARCH_17N    (MARCH_17N)
		) utils_sram_bist_inst(
			.clk          (clk),
			.nrst         (nrst),

			.bist         (bist),
			.bist_run     (bist_run_sync),

			.ce           (ce_bist),
			.we           (we_bist),
			.oe           (oe_bist),
			.addr         (addr_bist),
			.wdata        (wdata_bist),
			.rdata        (rdata_bist)
		);

	//========================================================================
	// SRAM scan shell instance
	//========================================================================

	wire                          ce_sram;
	wire          [NUM_PARTS-1:0] we_sram;
	wire          [NUM_PARTS-1:0] oe_sram;
	wire         [ADDR_WIDTH-1:0] addr_sram;
	wire    [SRAM_DATA_WIDTH-1:0] wdata_sram;
	wire    [SRAM_DATA_WIDTH-1:0] rdata_sram;

	utils_sram_scan_shell #(
			.NUM_PARTS  (NUM_PARTS),
			.DATA_WIDTH (SRAM_DATA_WIDTH),
			.ADDR_WIDTH (ADDR_WIDTH),
			.DEPTH      (DEPTH)
		) utils_sram_scan_shell_inst(
			.clk       (clk),
			.nrst      (nrst),

			.ce        (ce_sram),
			.we        (we_sram),
			.oe        (oe_sram),
			.addr      (addr_sram),
			.wdata     (wdata_sram),
			.rdata     (rdata_sram),

			.scan_mode (scan_mode)
		);

	//========================================================================
	// SRAM signals multiplexer
	//========================================================================

	assign ce_sram    = bist_run_sync ? ce_bist    : ce_mux;
	assign we_sram    = bist_run_sync ? we_bist    : we_mux;
	assign oe_sram    = bist_run_sync ? oe_bist    : oe_mux;
	assign addr_sram  = bist_run_sync ? addr_bist  : addr_mux;
	assign wdata_sram = bist_run_sync ? wdata_bist : wdata_extended;

	assign rdata_bist     = rdata_sram;
	assign rdata_extended = rdata_sram;

endmodule

