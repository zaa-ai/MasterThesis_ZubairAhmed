/**
 * Interface: timebase_info_if
 * 
 * interface containing all information regarding timebase e.g. 1us ticks, base_time, clkref_ok
 */
interface timebase_info_if;
	import	project_pkg::*;
	
	timebase_t	base_time;
	logic	clkref_ok;
	logic	tick_1us;
	logic	tick_1ms;
	
	modport	master (
			output base_time, clkref_ok, tick_1us, tick_1ms
		);
	
	modport	slave (
			input base_time, clkref_ok, tick_1us, tick_1ms
		);


endinterface


