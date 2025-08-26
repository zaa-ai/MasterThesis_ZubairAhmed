//
// Verilog interface BLDC_DRIVER_tb.pwm_generator_if
//
// Created:
//          by - tle.UNKNOWN (exsim01.elmos.de)
//          at - 09:06:16 07/08/15
//

module syncro_reg#(
    parameter SIZE  = 8
  ) (
		input	logic 				clk,
		input	logic 				rstn,
		input	logic [SIZE-1:0]	in,
		output	logic [SIZE-1:0]	test_out,
		output	logic [SIZE-1:0]	out
  );
	
	always_ff @(posedge clk, negedge rstn) begin
		if (!rstn) begin
			test_out	<= '0;
			out			<= '0;
		end else begin
			test_out	<= in;
			out			<= test_out;
		end
	end
endmodule

