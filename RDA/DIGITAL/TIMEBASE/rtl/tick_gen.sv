/**
 * Module: tick_gen
 * 
 * Module to generate a tick from a.clk_rst with a definded ratio
 */
module tick_gen #(
		parameter int unsigned ratio = 4					// ratio from tick to clock 
	)(
		clk_reset_if.slave	clk_rst,
		input	logic	reset_sync,				// synchronous reset signal (can also be used as enable)
		output	logic	tick_out
	);
	
	import common_lib_pkg::*;
	
	localparam	int		ratio_bits = num2width(ratio);
	typedef logic	[ratio_bits-1:0] counter_t;
	counter_t	cnt, cnt_nxt;	// counter
	
	localparam	counter_t final_counter_value = counter_t'(ratio - 1);
	
	/*###   counter   ######################################################*/
	always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0)  begin
			cnt		<= '0;
		end
		else begin
			cnt		<= cnt_nxt;
		end
	end
	
	always_comb begin
		if ((cnt == final_counter_value) || (reset_sync == 1'b1))
			cnt_nxt = '0;
		else
			cnt_nxt = cnt + counter_t'(1);
	end
	
	/*###   output tick generation   ######################################################*/
	assign tick_out = (cnt == final_counter_value) ? 1'b1 : 1'b0;
	
	
endmodule


