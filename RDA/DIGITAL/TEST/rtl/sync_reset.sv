/**
 * Module: sync_reset
 * 
 * module for synchronous reset generation
 */
module sync_reset(
		input	logic	clk,
		input	logic	rstn_async,
		output	logic	o_rstn,
		output	logic	o_rstn_clock_posedge
	);
	
	logic[1:0]	reset_debouncer;
	logic		reset_posedge;
	
	always_ff @(negedge clk or negedge rstn_async) begin
		if (rstn_async == 1'b0)  begin
			reset_debouncer	<= '0;
		end
		else begin
			reset_debouncer	<= {1'b1, reset_debouncer[1]};
		end
	end
	
	always_ff @(posedge clk or negedge rstn_async) begin
		if (rstn_async == 1'b0)  begin
			reset_posedge	<= '0;
		end
		else begin
			reset_posedge	<= reset_debouncer[0];
		end
	end
	
	assign	o_rstn = reset_debouncer[0];
	assign	o_rstn_clock_posedge = reset_posedge;
	
endmodule


