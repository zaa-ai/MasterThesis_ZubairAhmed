/**
 * Module: clkref_monitor
 * 
 * Module checking a reference clock for correct input
 */
module clkref_monitor import	common_lib_pkg::*; #(
		parameter	min_value = 17,
		parameter	max_value = 19,
		parameter	hysteresis = 2
	)(
		clk_reset_if.slave	clk_rst,
		clk_reset_if.slave	clkosc_rst,
		input	logic		i_clkref_edge,
		output	logic		o_clkref_ok
	);
	
	localparam cnt_max_width = num2width((max_value + 1));
	
	typedef logic[cnt_max_width-1:0] counter_t;
	
	logic		clkref_valid, clkref_valid_nxt;
	counter_t	cnt_clkref_edge, cnt_clkref_edge_nxt;

	int		limit_low;
	always_comb begin
		if (clkref_valid == 1'b1) begin
			limit_low = min_value - hysteresis;
		end
		else begin
			limit_low = min_value;
		end
	end
	
	int		limit_high;
	always_comb begin
		if (clkref_valid == 1'b1) begin
			limit_high = max_value + hysteresis;
		end
		else begin
			limit_high = max_value;
		end
	end
	
	always_ff @(posedge clkosc_rst.clk or negedge clkosc_rst.rstn) begin
		if (clkosc_rst.rstn == 1'b0)  begin
			cnt_clkref_edge		<= '0;
			clkref_valid		<= 1'b0;
		end
		else begin
			cnt_clkref_edge		<= cnt_clkref_edge_nxt;
			clkref_valid		<= clkref_valid_nxt;
		end
	end

	always_comb begin
		if (i_clkref_edge == 1'b1) begin					// highest priority: if new edge of reference clock is input -> reset counter
			cnt_clkref_edge_nxt = '0;
		end
		else begin
			if (cnt_clkref_edge <= counter_t'(limit_high))
				cnt_clkref_edge_nxt = cnt_clkref_edge + counter_t'(1);	// count if in between correct limits
			else
				cnt_clkref_edge_nxt = cnt_clkref_edge;				// default: stay at current value
		end
	end
	
	always_comb begin
		clkref_valid_nxt = clkref_valid;					// default: no change
		if (i_clkref_edge == 1'b1) begin					// if a new edge of the reference clock is detected, ...
			if ((cnt_clkref_edge <= counter_t'(limit_high)) && (cnt_clkref_edge >= counter_t'(limit_low)))	// ... and the counter is in the valid limits 
				clkref_valid_nxt = 1'b1;					// reference clock is judged valid
			else
				clkref_valid_nxt = 1'b0;					// if the counter and thus the reference clock is not in the limits, judge it as invalid
		end
		if (cnt_clkref_edge > counter_t'(limit_high))
			clkref_valid_nxt = 1'b0;
	end
	
	sync #(
			.SIZE        (1 )
		) i_sync_clkref_ok (
			.clk_rst     (clk_rst             ), 
			.i_in        (clkref_valid    ), 
			.o_test_out  ( ), 
			.o_out       (o_clkref_ok    ));
	
endmodule


