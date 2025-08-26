/**
 * Interface: clock_switch_if
 * 
 * interface for using a clock switch 
 */
interface clock_switch_if;
	logic	clock_osc;
	logic	clock_pll;
	logic	select_clock_pll;
	logic	clock_switched;
	logic	test_en;
	logic	test_sel;
	
	modport	timebase(
			output	select_clock_pll, test_en, test_sel,
			input	clock_switched
		);
	
	modport slave(
			input	clock_osc, clock_pll, select_clock_pll, test_en, test_sel,
			output	clock_switched
		);

endinterface


