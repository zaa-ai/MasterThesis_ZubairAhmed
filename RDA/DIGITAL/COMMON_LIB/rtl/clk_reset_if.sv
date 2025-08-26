/****************************************************************************
 * clk_reset_if.sv
 ****************************************************************************/

/**
 * Interface: clk_reset_if
 * 
 * Interface consisting of a clock and the corresponding reset
 */
interface clk_reset_if;
	logic	clk, rstn;
	
	modport master (
			output clk, rstn
		);
	
	modport slave (
			input clk, rstn
		);
endinterface


