/**
 * Module: ecc_edge_detection
 *
 * make an edge detection from ECC error interface
 */
module ecc_edge_detection #(parameter WIDTH = 1)(
		clk_reset_if.slave	clk_rst,
		ecc_error_if.slave	ecc_in,
		ecc_error_if.master	ecc_out
	);
	
	logic[WIDTH-1:0]	single_error;
	logic[WIDTH-1:0]	double_error;
			
	always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (!clk_rst.rstn) begin
			single_error <= '0;
			double_error <= '0;
		end
		else begin
			single_error <= ecc_in.single_error;
			double_error <= ecc_in.double_error;
		end
	end
	
	assign	ecc_out.single_error = ecc_in.single_error & ~single_error;
	assign	ecc_out.double_error = ecc_in.double_error & ~double_error;

endmodule