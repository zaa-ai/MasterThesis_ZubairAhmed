
`timescale 1ns/1ns
`include "tech.v"

module por #(
		parameter POR_TIME_NS = 100
	)(
`ifdef target_technology_FPGA
		input        clk,
`endif
		output logic npor
	);

`ifdef target_technology_FPGA

	FD_1 npor_ff_inst(.Q(npor), .C(clk), .D(1'b1));

`else

	initial begin
		npor = 1'b0;
		#(POR_TIME_NS);
		npor = 1'b1;
	end

`endif

endmodule

