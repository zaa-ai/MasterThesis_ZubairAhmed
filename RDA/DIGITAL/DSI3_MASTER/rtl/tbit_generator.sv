/**
 * Module: tbit_generator
 * 
 * Tick generator for t_Bit_
 */
module tbit_generator #(
		parameter SHIFT_WIDTH=8
	)(
		clk_reset_if.slave	clk_rst,
		input	logic	i_tick,
		input	logic[SHIFT_WIDTH-1:0]	i_shift,
		output	logic	o_tick
	);
	
	typedef logic	[SHIFT_WIDTH-1:0] counter_t;
	counter_t	cnt, cnt_nxt;	// counter
	logic	tick, tick_next;
	
	/*###   counter   ######################################################*/
	always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0)  begin
			cnt		<= '0;
			tick	<= 1'b1;
		end
		else begin
			cnt		<= cnt_nxt;
			tick	<= tick_next;
		end
	end
	
	always_comb begin
		if (i_shift != '0) begin
			if (i_tick == 1'b1) begin
				cnt_nxt = counter_t'(i_shift);
			end
			else begin
				if (cnt > counter_t'(0))
					cnt_nxt = cnt - counter_t'(1);
				else
					cnt_nxt =  cnt;
			end
		end
		else begin
			cnt_nxt =  cnt;
		end
	end
	
	assign	o_tick = tick_next & ~tick;
	/*###   output tick generation   ######################################################*/
	always_comb begin
		tick_next = (cnt == counter_t'(1)) ? 1'b1 : 1'b0;
	end

endmodule
