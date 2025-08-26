/**
 * Module: deb
 * 
 * Debouncer, similiar to debounce_rtl.vhd
 * 
 */
module deb #(
		parameter DEBOUNCE_TIME = 4,
		parameter RESET_VALUE = 1'b0
	)(
		//interfaces
		clk_reset_if.slave clk_rst,
		//inputs
		input logic i_in,
		//outputs
		output logic o_out
	);

	localparam COUNTER_SIZE = $clog2(DEBOUNCE_TIME-1);
	
	logic  prev_signal;
	logic [COUNTER_SIZE-1:0] counter;
	
	always_ff@(posedge clk_rst.clk, negedge clk_rst.rstn)
	begin
		if (clk_rst.rstn == 1'b0) begin
			o_out <= RESET_VALUE;
			prev_signal <= RESET_VALUE;
			counter <= COUNTER_SIZE'(DEBOUNCE_TIME - 1);
	
		end /* if (clk_rst.rstn == 1'b0) */
		else begin
			prev_signal <= i_in;
			if (i_in == prev_signal) begin
				if (counter == 0) begin
					o_out <= prev_signal;
				end /* if (counter == 0) */
				else begin
					counter <= COUNTER_SIZE'(counter - 1);
				end
			end /* if (i_in == prev_signal) */
			else begin
			counter <= COUNTER_SIZE'(DEBOUNCE_TIME - 1);
			end
		end
	end			
endmodule
