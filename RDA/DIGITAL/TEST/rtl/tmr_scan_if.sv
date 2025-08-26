/**
 * Interface: tmr_scan
 * 
 * interface for scan test modes and corresponding signals
 */
interface tmr_scan_if;
	logic	scan;
	logic	vdd_voltage_divider_disable;
	logic	vdd_disable;
	logic	vdd_load_disable;
	logic	disable_osc;
	
	logic	scan_clock;
	logic	scan_reset;
	
	modport master(
			input	scan_clock, scan_reset,
			output	scan, vdd_voltage_divider_disable, vdd_disable, vdd_load_disable, disable_osc
		);

endinterface


