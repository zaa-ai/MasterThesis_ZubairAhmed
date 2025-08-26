
`timescale 1ns/10ps

module sync_sram #(
		parameter NUM_PARTS  = 2,
		parameter DATA_WIDTH = 16,
		parameter ADDR_WIDTH = 10,
		parameter DEPTH      = 1024
		)(
		input                           clk,    // clk

		input                           ce,     // chip enable
		input           [NUM_PARTS-1:0] we,     // part write enable
		input           [NUM_PARTS-1:0] oe,     // part output enable
		input          [ADDR_WIDTH-1:0] addr,   // address
		input          [DATA_WIDTH-1:0] wdata,  // data in
		output         [DATA_WIDTH-1:0] rdata   // data out
		);

	`include "vlog_functions_inc.sv"

	//	localparam ADDR_WIDTH = num2width(DEPTH-1);

	// respect simulation model control signal to clock hold times ...

	wire                  ce_delayed;
	wire  [NUM_PARTS-1:0] we_delayed;
	wire  [NUM_PARTS-1:0] oe_delayed;
	wire [ADDR_WIDTH-1:0] addr_delayed;
	wire [DATA_WIDTH-1:0] wdata_delayed;

	`ifndef VCS
		`define SYNC_SRAM_CONTROL_DELAY
	`else
		`define SYNC_SRAM_CONTROL_DELAY #1
	`endif

	assign `SYNC_SRAM_CONTROL_DELAY ce_delayed    = ce;
	assign `SYNC_SRAM_CONTROL_DELAY we_delayed    = we;
	assign `SYNC_SRAM_CONTROL_DELAY oe_delayed    = oe;
	assign `SYNC_SRAM_CONTROL_DELAY addr_delayed  = addr;
	assign `SYNC_SRAM_CONTROL_DELAY wdata_delayed = wdata;

	logic wen_sram;
	assign wen_sram = ~we_delayed;

	// technology dependent SRAM instance generate block ...

	SRAM_3072X23U18 sram_inst (
			.Q    (rdata),
			.CLK  (~clk),
			.CEN  (~ce_delayed),
			.WEN  (~we_delayed),
			.A    (addr_delayed),
			.D    (wdata_delayed)
		);

endmodule

