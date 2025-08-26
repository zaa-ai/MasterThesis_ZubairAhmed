/**
 * Module: pll_monitor
 * 
 * module for monitoring PLL clock
 */
module pll_monitor(
		clk_reset_if.slave	clk_rst,
		input	logic		i_clkref_rising,
		input	logic		i_clkpll_div_rising,
		input	logic		i_enable,
		output	logic		o_pll_locked
	);
	
	// monitor clkref and clkpll_div -> is ok, when rising edges are the same
	
	logic 		clkref_rising_previous;
	logic[1:0]	clkpll_div_rising_previous;
	logic		clkpll_div_to_check;
	
	assign		clkpll_div_to_check = |({i_clkpll_div_rising, clkpll_div_rising_previous});
	
	always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0)  begin
			clkref_rising_previous		<= 1'b0;
			clkpll_div_rising_previous	<= 2'd0;
		end
		else begin
			clkref_rising_previous		<= i_clkref_rising;
			clkpll_div_rising_previous	<= {clkpll_div_rising_previous[0], i_clkpll_div_rising};
		end
	end
		
	logic[3:0]	debounce_counter, debounce_counter_nxt;
	always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0)  begin
			debounce_counter		<= '0;
		end
		else begin
			debounce_counter		<= debounce_counter_nxt;
		end
	end	
	
	always_comb begin
		debounce_counter_nxt = debounce_counter;
		if (clkref_rising_previous == 1'b1) begin
			if (clkpll_div_to_check == 1'b1) begin
				if (debounce_counter != '1) begin
					debounce_counter_nxt = debounce_counter + 4'd1;
				end
			end
			else begin
				debounce_counter_nxt = '0;
			end
		end
		if (i_enable == 1'b0) begin
			debounce_counter_nxt = '0;
		end
	end
	
	assign	o_pll_locked = (debounce_counter == '1) ? 1'b1 : 1'b0 ;


endmodule


