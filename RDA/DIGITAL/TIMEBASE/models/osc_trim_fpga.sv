//`timescale 1ps/1ps

module osc_trim_fpga #(
		parameter trim_size			=  8,
		parameter realtime tfmin	= 27.78ns,
		parameter realtime tstep	=  0.0249ns
	)(
		input logic [trim_size -1:0] trim,
		input enable,
		output clk_out,
		input real vcc,
		input real vss,
		input real vsub
	);
	
	parameter period=27.7778ns;

	reg	clk = 1'b0;
	
	always begin
		if (enable == 1'b1)
			#period clk = ~clk; // toggle clock
		else 
			#period clk = 1'b0;
	end

	// assign clock to output if vcc is present
	assign clk_out = (vcc > 1.3) ? clk : 1'b0; 
	
endmodule
