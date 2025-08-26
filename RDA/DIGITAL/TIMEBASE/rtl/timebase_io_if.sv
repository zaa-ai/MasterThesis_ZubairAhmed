/**
 * Interface: timebase_io_if
 * 
 * interface containing all I/O signals to analog part of oscillator/PLL block
 */
interface timebase_io_if;
	import project_pkg::*;
	
	logic	clkref, clkref_div;
	logic	clkpll, clkpll_div;
	
	trim_osc_f_t	trim_osc_f;			// trim vector for oscillator
	trim_osc_tcf_t	trim_osc_tcf;			// trim vector for oscillator
	logic	pll_on;
	logic	pll_hold;
	
	logic	pll_down_mon, pll_up_mon, pll_lock_mon;
	
	modport master(
		input	clkref, clkpll, clkpll_div,
		output	clkref_div,
		output	pll_on, pll_hold,
		output	trim_osc_f, trim_osc_tcf,
		input	pll_down_mon, pll_up_mon, pll_lock_mon
	);
	
	modport slave(
		output	clkref, clkpll, clkpll_div,
		input	clkref_div,
		input	pll_on, pll_hold,
		input	trim_osc_f, trim_osc_tcf,
		output	pll_down_mon, pll_up_mon, pll_lock_mon
	);

endinterface


