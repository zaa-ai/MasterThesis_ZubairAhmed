/**
 * Interface: tmr_out_osc
 * 
 * interface for digital outputs via TMR_OUT of oscillator/PLL block
 */
interface tmr_out_osc_if;
	logic	clkref_filtered, clkref_divided;
	logic	pll_down_mon, pll_up_mon, pll_lock_mon, clkpll_div;
	logic	clkosc_divided, clkpll_divided, clksys_divided;
	logic	clkosc, clkpll, clksys;
	
	// internal signals
	logic	clkref_ok, pll_locked;
	
	logic[13:0]	value;
	
	logic	clock_selected;
	
	modport master (
			output	clkref_filtered, clkref_divided,
			output	pll_down_mon, pll_up_mon, pll_lock_mon, clkpll_div,
			output	clkosc_divided, clkpll_divided, clksys_divided,
			output	clkosc, clkpll, clksys,
			output	clkref_ok, pll_locked,
			input	clock_selected
		);
	
	modport slave (
			input	value
		);
	
	assign	value = {
			// internal
			pll_locked, clkref_ok,
			// monitoring signals
			pll_lock_mon, pll_up_mon, pll_down_mon, clkpll_div,
			// divided clocks
			clksys_divided, clkpll_divided, clkosc_divided, 
			// clocks
			clksys, clkpll, clkosc, 
			// CLKREF
			clkref_divided, clkref_filtered};

endinterface
