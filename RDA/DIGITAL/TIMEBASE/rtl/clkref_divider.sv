/**
 * Module: clkref_divider
 * 
 * divider for CLKREF
 * 	i_div_config= 0 -> :1 (0.5MHz)
 * 				= 1 -> :2 (1.0MHZ)
 * 				= 2 -> :4 (2.0MHZ)
 * 				= 3 -> :8 (4.0MHZ)
 */
module clkref_divider(
		input	logic	i_clkref,
		input	logic	i_rstn,
		input	logic[1:0]	i_div_config,
		output	logic	o_clkref_div
	);
	
	logic clkref_divided[3:0];
	
	assign	clkref_divided[0] = i_clkref;
	
	assign	o_clkref_div = clkref_divided[i_div_config];
	
	generate
		genvar i;
		for(i=3; i>0; i--) begin : generate_clocks
			always_ff @(posedge clkref_divided[i-1] or negedge i_rstn) begin
				if (i_rstn == 1'b0)  begin
					clkref_divided[i] <= 1'b0;
				end
				else begin
					clkref_divided[i] <= ~clkref_divided[i];
				end
			end
		end
	endgenerate

endmodule


