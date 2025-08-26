//`timescale 1ps/1ps

module osc_trim #(
		parameter trim_size			=  8,
		parameter realtime tfmin	= 27.78ns,
		parameter realtime tstep	=  0.0249ns
	)(
		input	logic [trim_size -1:0] trim,
		input	logic	[2:0]	trim_tcf, //TODO: add temperature dependency
		input	logic	enable,
		input	logic	TST_OSC_SFMAX,
		input	logic	TST_OSC_SFMIN,
		
		output	logic	clk_out,
		output	logic	osc_ready,
		input real vdd,
		input real vss,
		input real vsub
//		,input	logic	ATST_OSC
		
//		,inout	AOUT
	);
	
	bit	 [trim_size -1:0] trim_internal;
	reg	clk = 1'b0;

	realtime	per_int = tfmin;
    
	always_comb begin
		trim_internal = ($isunknown(trim)) ? '0 : trim;
		if (TST_OSC_SFMIN == 1'b1) begin
			trim_internal = '0;
		end
		if (TST_OSC_SFMAX == 1'b1) begin
			trim_internal = '1;
		end
	end
	
	always@(enable) begin
		if (enable == 1'b1) begin
			#($urandom_range(50000,10000)*1ns) osc_ready = 1'b1;
		end
		else begin
			osc_ready = 1'b0;
		end
	end
	
	always@(trim_internal) begin
		per_int = tfmin - (tstep*trim_internal);
	end
	
	always begin
		if (enable === 1'b1)
			#per_int clk = ~clk; // toggle clock
		else #per_int clk = 1'b0;
	end
	
	logic	gate_clk;
	assign	gate_clk = ((vdd - (vss-vsub)) > 1.3) ? 1'b1 : 1'b0;

	assign clk_out = gate_clk & clk; 
	
endmodule
