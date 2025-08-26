/**
 * Module: edge_detect
 * 
 * detect an edge of the input signal
 */
module edge_detect #(
		parameter	detect_rising_edge = 1'b1
	)(
		clk_reset_if.slave	clk_rst,
		input	logic		i_signal,
		output	logic		o_edge
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
	
	if (detect_rising_edge == 1'b1) begin : generate_posedge
		assign	o_edge = i_signal & ~previous;
	end
	else begin : generate_nededge
		assign	o_edge = ~i_signal & previous;
	end

endmodule


