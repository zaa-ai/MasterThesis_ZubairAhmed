/**
 * Module: dsi3_receive_counter
 * 
 * Counter
 */
module dsi3_receive_counter (
		clk_reset_if.slave	clk_rst,
		input	logic		i_count,
		input	logic		i_enable,
		input	logic		i_restart,
		output	logic[7:0]	o_cnt
	);
	
	logic[7:0]	cnt, cnt_nxt;
	
	always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0)  begin
			cnt <= '0;
		end
		else begin
		if (((i_count == 1'b1) && (i_enable == 1'b1)) || ((i_restart & ~i_enable) == 1'b1))
			cnt <= cnt_nxt;
		end
	end
	
	always_comb begin
		if (cnt != '1)
			cnt_nxt = cnt + 8'd1;
		else
			cnt_nxt = cnt;
		if (i_restart == 1'b1)
			cnt_nxt = '0;
	end

	assign o_cnt = cnt;

endmodule


