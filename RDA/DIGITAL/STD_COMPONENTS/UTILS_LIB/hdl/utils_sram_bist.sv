
`timescale 1ns/1ns

module utils_sram_bist #(
		parameter NUM_PARTS  = 4,
		parameter DEPTH      = 256,
		parameter DATA_WIDTH = 32,
		parameter ADDR_WIDTH = 8,
		parameter MARCH_17N  = 0
		)(
		input                               clk,
		input                               nrst,

		bist_if.sp                          bist,
		output                              bist_run,

		output reg                          ce,
		output reg          [NUM_PARTS-1:0] we,
		output reg          [NUM_PARTS-1:0] oe,
		//		output reg [num2width(DEPTH-1)-1:0] addr,
		output reg         [ADDR_WIDTH-1:0] addr,
		output             [DATA_WIDTH-1:0] wdata,
		input              [DATA_WIDTH-1:0] rdata
		);

	`include "vlog_functions_inc.sv"

	//	localparam ADDR_WIDTH = num2width(DEPTH-1);

	localparam ABITS  = (NUM_PARTS > 1) ? num2width(NUM_PARTS-1) : 0;  // number of address LSBs used for vector extension

	localparam CORE_ADDR_WIDTH = ADDR_WIDTH + ABITS;
	localparam CORE_PART_WIDTH = DATA_WIDTH / NUM_PARTS;

	wire                        core_ce;
	wire                        core_we;
	wire                        core_oe;
	wire  [CORE_ADDR_WIDTH-1:0] core_addr;
	wire  [CORE_PART_WIDTH-1:0] core_wdata;
	logic [CORE_PART_WIDTH-1:0] core_rdata;

	generate
		if (MARCH_17N) begin : march_17n

			utils_sram_bist_march_17n #(
					.ABITS      (ABITS),
					.APARTS     (NUM_PARTS),
					.DEPTH      (DEPTH),
					.ADDR_WIDTH (CORE_ADDR_WIDTH),
					.PART_WIDTH (CORE_PART_WIDTH)
				) utils_sram_bist_march_inst(
					.clk      (clk),
					.nrst     (nrst),

					.bist     (bist),
					.bist_run (bist_run),

					.ce       (core_ce),
					.we       (core_we),
					.oe       (core_oe),
					.addr     (core_addr),
					.wdata    (core_wdata),
					.rdata    (core_rdata)
				);

		end
		else begin : march_22n

			utils_sram_bist_march_22n #(
					.ABITS      (ABITS),
					.APARTS     (NUM_PARTS),
					.DEPTH      (DEPTH),
					.ADDR_WIDTH (CORE_ADDR_WIDTH),
					.PART_WIDTH (CORE_PART_WIDTH)
				) utils_sram_bist_march_inst(
					.clk      (clk),
					.nrst     (nrst),

					.bist     (bist),
					.bist_run (bist_run),

					.ce       (core_ce),
					.we       (core_we),
					.oe       (core_oe),
					.addr     (core_addr),
					.wdata    (core_wdata),
					.rdata    (core_rdata)
				);

		end
	endgenerate

	//==========================================================================

	assign wdata = {NUM_PARTS{core_wdata}};

	generate
		if (ABITS) begin : abits

			logic [ABITS-1:0] core_addr_last;

			always_ff @(negedge nrst or posedge clk)
			begin
				if (!nrst) begin
					core_addr_last <= '0;
				end
				else begin
					core_addr_last <= core_addr[ABITS-1:0];
				end
			end

			always_comb
			begin
				ce = core_ce;
				we = '0;
				oe = '0;
				we[core_addr[0 +: ABITS]] = core_we;
				oe[core_addr[0 +: ABITS]] = core_oe;
				addr = core_addr >> ABITS;
				core_rdata = rdata[CORE_PART_WIDTH * core_addr_last[0 +: ABITS] +: CORE_PART_WIDTH];
			end

		end
		else begin : no_abits
			// DMOS: due to one cycle access we have to sample rdata for comparision 23 additional ff's :(
			logic [DATA_WIDTH-1:0] rdata_sampled;
			always_comb
			begin
				ce = core_ce;
				we = core_we;
				oe = core_oe;
				addr = core_addr;
				core_rdata = rdata_sampled;
			end

			always_ff @(negedge nrst or posedge clk)
			begin
				if (!nrst) begin
					rdata_sampled <= '0;
				end
				else begin
					if (core_oe == 1'b1) begin
						rdata_sampled <= rdata;
					end
				end
			end
		end
	endgenerate

endmodule

