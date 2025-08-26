/**
 * Module: vcc_deb
 * 
 * module for VCC debouncing
 */
module vcc_deb #(
		parameter int unsigned DEBOUNCE_TIME = 4,
		parameter RESET_VALUE = 1'b0		
	) (
		clk_reset_if.slave clk_rst,
		input logic i_in,
		input logic i_debounce_tick,
		output logic o_out
	);
	
	localparam int counter_length = $clog2(DEBOUNCE_TIME+1);
	typedef logic[counter_length-1:0] counter_t;
	
	logic prev_signal;
	counter_t counter;
		
	
	always_ff@(posedge clk_rst.clk, negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0) begin
			o_out <= RESET_VALUE;
			prev_signal <= RESET_VALUE;
			counter <= counter_t'(DEBOUNCE_TIME - 1);
		end
		else begin
			prev_signal <= i_in;
			if (i_in == 1'b0) begin
				o_out <= 1'b0;
				counter <= counter_t'(DEBOUNCE_TIME - 1);
			end
			else begin
				if (i_in == prev_signal) begin
					if (i_debounce_tick == 1'b1) begin
						if (counter == counter_t'(0)) begin
							o_out <= prev_signal;
						end
						else begin
							counter <= counter - counter_t'(1);
						end
					end
				end
				else begin
					counter <= counter_t'(DEBOUNCE_TIME - 1);
				end
			end
		end 
	end	
endmodule
