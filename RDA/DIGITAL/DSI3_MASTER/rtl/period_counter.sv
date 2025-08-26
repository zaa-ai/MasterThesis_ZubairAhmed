/**
 * Module: period_counter
 * 
 * counter for counting DSI3 PDCM periods
 */
module period_counter import dsi3_pkg::*; import project_pkg::*; (
		clk_reset_if.slave			clk_rst,
		input	data_t				i_new_period_value,
		input	logic				i_start,
		input	logic				i_stop,
		output	logic				o_receive_timeout,
		output	logic				o_running
	);
	
	logic	tick_1us, tick_1us_one_clock_earlier;
	logic	running, running_next;
	
	typedef logic	[4:0] counter_t;
	counter_t	tick_cnt, tick_cnt_nxt;	// counter
	
	localparam	counter_t final_counter_value = counter_t'(17);
	
	data_t	period_counter, period_counter_next;
	
	always_comb begin
		if ((tick_cnt == final_counter_value) || ((i_start | ~o_running ) == 1'b1))
			tick_cnt_nxt = '0;
		else
			tick_cnt_nxt = tick_cnt + counter_t'(1);
	end
	assign tick_1us = (tick_cnt == final_counter_value) ? 1'b1 : 1'b0;
	assign tick_1us_one_clock_earlier = (tick_cnt == (final_counter_value-counter_t'(1))) ? 1'b1 : 1'b0;
	
	//FIXME: some issues with clock gating and scan coverage. something with o_running 
	always_ff@(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0) begin
			running        <= 1'b0;
			tick_cnt	   <= '0;
			period_counter <= '0;
		end
		else begin
			running        <= running_next;
			tick_cnt	   <= tick_cnt_nxt;
			period_counter <= period_counter_next;
		end
	end
	
	always_comb begin
		period_counter_next = period_counter;
		if ((i_start == 1'b1) || (i_stop == 1'b1)) begin
			period_counter_next = i_new_period_value - data_t'(1);
		end
		else begin
			if (period_counter > '0) begin
				if (tick_1us == 1'b1) begin
					period_counter_next = period_counter - data_t'(1);
				end
			end
		end
	end
	
	always_comb begin
		running_next = running;
		if ((period_counter == '0) && (tick_1us_one_clock_earlier == 1'b1)) begin
			running_next = 1'b0;
		end
		if ((i_start == 1'b1) && (i_stop == 1'b0)) begin
			running_next = 1'b1;
		end
		if (i_stop == 1'b1) begin
			running_next = 1'b0;
		end
	end
	
	assign	o_running = running;
	
	assign	o_receive_timeout = (period_counter == data_t'(5)) ? tick_1us : 1'b0;
	
endmodule
