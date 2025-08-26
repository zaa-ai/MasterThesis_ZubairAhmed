/**
 * Module: dsi3_filter
 * 
 * Filter for DSI3 inputs
 */
module dsi3_chip_filter_for_dm  import dsi3_pkg::*; #(
		parameter	debounce_length = 8
	) (
		clk_reset_if.slave	clk_rst,
		input	logic[1:0]	i_dsi3,										// DSI3 input from receiver
		input	logic		i_tick_1us,
		input	logic		i_enable,
		output	logic		o_filtered
	);
	
	dsi3_chip_if chip_in();
	
	dsi3_chip_converter i_dsi3_chip_converter (
		.receiver_output  (i_dsi3 ), 
		.dsi3_chip_out    (chip_in.master   )
	);
	
	typedef logic[4:0]	counter_t;
	counter_t	cnt, cnt_nxt;

	always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0)  begin
			cnt	<= '0;
		end
		else begin
			cnt	<= cnt_nxt;
		end
	end
	
	always_comb begin
		cnt_nxt = cnt;
		if (i_enable == 1'b1) begin
			if ((chip_in.chip == C1) || (chip_in.chip == C2)) begin
				if (i_tick_1us == 1'b1) begin
					cnt_nxt = cnt + counter_t'('d1);
				end
			end
			else begin
				if (cnt > 5'd0) begin
					if (i_tick_1us == 1'b1) begin
						cnt_nxt = cnt - counter_t'('d1);
					end
				end
				else
					cnt_nxt = '0;
			end
		end
		else
			cnt_nxt = '0;
	end
	
	assign	o_filtered = (int'(cnt) >= debounce_length) ? 1'b1 : 1'b0;

endmodule
