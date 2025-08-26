/**
 * Module: osc_top
 * 
 * model of the oscillator and PLL
 */
module osc_top(
//		inout	AOUT,
		input	logic [6:0] ATST_PLL,
		input	logic		ATST_OSC,
		
		input 	logic		CLKREF,
		input	logic		CLKREF_DIV,
		input 	logic		RESB,
		
		input	logic		ON_OSC,
		input	logic		ON_PLL,
		input	logic		PLL_HOLD,
		input	logic[6:0]	OSC_F_TRIM,
		input	logic[2:0]	OSC_TCF_TRIM,
		input	logic		TST_OSC_SFMAX,
		input	logic		TST_OSC_SFMIN,
		
		output	logic		CLKREF_FILT,
		output	logic		CLKOSC,
		output	logic		CLKPLL,
		output	logic		CLKPLL_DIV,
		output	logic		PLL_LOCK_MON,
		output	logic		PLL_UP_MON,
		output	logic		PLL_DOWN_MON,
		output	logic		OSC_READY,
		
		input 	real		SUB,
		input 	real		VDD,
		input 	real		GND		
		
	);
	
	clkref_filter XCLKREF_LPF_0 (
		.CLKREF       (CLKREF      ), 
		.CLKREF_FILT  (CLKREF_FILT ));
	
	pll_top u_pll (
			.RESB          (RESB         ), 
			.ON_PLL        (ON_PLL       ), 
			.CLKREF        (CLKREF_DIV   ), 
			.PLL_HOLD      (PLL_HOLD     ), 
			.CLKPLL        (CLKPLL       ), 
			.CLKPLL_DIV    (CLKPLL_DIV   ), 
			.PLL_LOCK_MON  (PLL_LOCK_MON ), 
			.PLL_UP_MON    (PLL_UP_MON   ), 
			.PLL_DOWN_MON  (PLL_DOWN_MON ), 
			.ATST_PLL      (ATST_PLL     ),
//			.AOUT          (AOUT         ),
			.GND			(GND),
			.VDD			(VDD)
		);

	osc_trim #(
			.trim_size(7),
			.tfmin(41.6ns),
			.tstep(0.184ns)
		) xosc_trim (
			.vss(GND),
			.vsub(SUB),
			.vdd(VDD),
			.trim(OSC_F_TRIM),
			.trim_tcf (OSC_TCF_TRIM),
			.TST_OSC_SFMAX(TST_OSC_SFMAX),
			.TST_OSC_SFMIN(TST_OSC_SFMIN),
			.enable(ON_OSC),
			.clk_out(CLKOSC),
			.osc_ready(OSC_READY)
//			,.ATST_OSC	   (ATST_OSC     )
//			,.AOUT(AOUT)
		);
	
	always@(SUB) begin
		if (SUB != 0.0) begin
			$fatal("SUB is not 0.0. SUB=%f", SUB);
		end
	end
	
	always@(GND) begin
		if (GND != 0.0) begin
			$fatal("GND is not 0.0. GND=%f", GND);
		end
	end

endmodule


