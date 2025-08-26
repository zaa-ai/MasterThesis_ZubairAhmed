
`timescale 1ns/10ps

module sync_sram_slice #(
		parameter DATA_WIDTH = 16,
		parameter DEPTH      = 1024
	)(
		input                           clk,    // clk

		input                           ce,     // chip enable
		input                           we,     // write enable
		input  [num2width(DEPTH-1)-1:0] addr,   // address
		input          [DATA_WIDTH-1:0] wdata,  // data in
		output         [DATA_WIDTH-1:0] rdata   // data out
	);

	`include "vlog_functions_inc.sv"

	localparam ADDR_WIDTH = num2width(DEPTH-1);

	reg  [DATA_WIDTH-1:0] ram[(2**ADDR_WIDTH)-1:0];
	reg  [ADDR_WIDTH-1:0] raddr;

	always @(posedge clk)
	begin
		if (ce & we) begin
			ram[addr] <= wdata;
		end
		raddr <= addr;
	end

	assign rdata = ram[raddr];

endmodule

