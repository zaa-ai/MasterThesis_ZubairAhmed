/**
 * Module: tick_div
 * 
 * Module to divide a tick by x in a clock domain
 */
module tick_div #(
		parameter	int unsigned ratio = 4						// ratio between outgoing and incoming clock tick
	)(
		clk_reset_if.slave clk_rst,						// clock and reset
		input	logic	tick_in,						// incoming clock tick
		input	logic	reset_sync,						// synchronous reset signal (can also be used as enable)
		output	logic	tick_out						// outgoing clock tick
	);
	
	import common_lib_pkg::*;
	
	localparam	int		ratio_bits = num2width(ratio);
	typedef logic	[ratio_bits-1:0] counter_t;
	counter_t	cnt, cnt_nxt;			// counter for counting incoming ticks
	
	/*###   counter   ######################################################*/
	always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0)  begin
			cnt		<= '0;
		end
		else begin
			if (tick_in == 1'b1)
				cnt		<= cnt_nxt;
		end
	end
	
	always_comb begin
		if ((cnt == (counter_t'(ratio -1) )) || (reset_sync == 1'b1))
			cnt_nxt = '0;
		else
			cnt_nxt = cnt + counter_t'(1);
	end
	
	/*###   output tick generation   ######################################################*/
	assign tick_out = (cnt == counter_t'(ratio-1)) ? tick_in : 1'b0;
	
endmodule


