/**
 * Module: sync
 * 
 * Module for synchronization of a signal
 * 
 * SIZE: bit width of the signal
 */
module sync#(
    parameter SIZE  = 1
  ) (
		clk_reset_if.slave			clk_rst,
		input	logic [SIZE-1:0]	i_in,
		output	logic [SIZE-1:0]	o_test_out,
		output	logic [SIZE-1:0]	o_out
  );
	
	always_ff @(posedge clk_rst.clk, negedge clk_rst.rstn) begin
		if (!clk_rst.rstn) begin
			o_test_out	<= '0;
			o_out		<= '0;
		end else begin
			o_test_out	<= i_in;
			o_out		<= o_test_out;
		end
	end
endmodule

