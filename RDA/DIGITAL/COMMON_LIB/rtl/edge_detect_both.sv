/**
 * Module: edge_detect
 * 
 * detect an edge of the input signal
 */
module edge_detect_both (
		clk_reset_if.slave	clk_rst,
		input	logic		i_signal,
		output	logic		o_pos_edge,
		output	logic		o_neg_edge
	);
	
	logic	previous;
	
	always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0)  begin
			previous <= 1'b0;
		end
		else begin
			previous		<= i_signal;
		end
	end
	
	assign	o_pos_edge = i_signal & ~previous;
	assign	o_neg_edge = ~i_signal & previous;

endmodule


