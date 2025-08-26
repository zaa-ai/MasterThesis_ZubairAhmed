//
// Verilog interface BLDC_DRIVER_tb.pwm_generator_if
//
// Created:
//          by - tle.UNKNOWN (exsim01.elmos.de)
//          at - 09:06:16 07/08/15
//

module sync_pad(
		clk_reset_if.slave			clk_rst,
		pad_int_if.sync				pad
	);
	
	logic	test_out;
	logic	out;
	
	always_ff @(posedge clk_rst.clk, negedge clk_rst.rstn) begin
		if (!clk_rst.rstn) begin
			test_out	<= '0;
			out			<= '0;
		end else begin
			test_out	<= pad.in_a;
			out			<= test_out;
		end
	end
	
	assign	pad.test_signal = test_out;
	assign	pad.in_s = out;
	
endmodule

