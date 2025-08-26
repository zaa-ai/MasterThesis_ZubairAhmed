`define clk_def(_clock_half_period_) clk_reset_if	clk_rst (); \
logic enable_clk; \
time clock_period_half = _clock_half_period_; \
task set_por(); \
		clk_rst.rstn = 1'b0; \
		#50ns; \
		clk_rst.rstn = 1'b1; \
		#50ns; \
endtask \
initial begin \
	clk_rst.clk = 1'b0; \
	enable_clk = 1'b0; \
	clock_period_half = _clock_half_period_; \
	set_por(); \
	forever begin \
		if (enable_clk) begin \
			clk_rst.clk = 1'b0; \
			#(clock_period_half); \
			clk_rst.clk = 1'b1; \
			#(clock_period_half); \
		end \
		else begin \
			@(posedge enable_clk); \
		end \
	end \
end \
task wait_for_n_clocks(int n); \
	repeat (n) begin \
		@(posedge clk_rst.clk); \
	end \
	#10ns; \
endtask

`define tick_gen logic tick_1us, tick_3MHz, tick_1ms; \
tick_gen #(	.ratio (6    )	) i_tick_1_3us ( .clk_rst   (clk_rst.slave  ), .reset_sync(1'b0 ), .tick_out  (tick_3MHz)	); \
tick_div #(	.ratio (3    )	) i_tick_1us ( .clk_rst   (clk_rst.slave  ), .tick_in   (tick_3MHz), .reset_sync(1'b0 ), .tick_out  (tick_1us )); \
tick_div #(	.ratio (1000 )	) i_tick_1ms ( .clk_rst   (clk_rst.slave  ), .tick_in   (tick_1us ), .reset_sync(1'b0 ), .tick_out  (tick_1ms ));
