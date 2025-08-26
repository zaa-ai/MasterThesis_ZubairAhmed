/**
 * Module: clk_div
 * 
 * module for dividing clocks to generate a tick signal
 */
module clk_div #(
			parameter	factor=8
		)
		(
			clk_reset_if.slave clk_rst,
			input	logic	i_enable,
			output	logic	clk_divided
		);
	import common_lib_pkg::*;
	
	localparam	cnt_width = num2width(factor);
	typedef logic	[cnt_width-1:0]	counter_t;
	
	logic	tick;
	counter_t	cnt, cnt_nxt;
	
	always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0)  begin
			cnt<= '0;
			clk_divided <= '0;
		end
		else begin
			if (i_enable == 1'b1) begin
				cnt<= cnt_nxt;
				if (tick) begin
					clk_divided <= ~clk_divided;
				end
			end
		end
	end
	
	always_comb begin
		cnt_nxt = cnt + counter_t'(1);
		tick = 1'b0;
		if (cnt == counter_t'(factor - 1)) begin
			cnt_nxt = '0;
			tick = 1'b1;
		end
	end

endmodule


