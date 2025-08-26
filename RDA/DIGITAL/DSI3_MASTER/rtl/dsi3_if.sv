/**
 * Interface: dsi3_chip_if
 * 
 * DSI3 interface containing a chip
 */
interface dsi3_chip_if;
	dsi3_pkg::dsi3_chip chip;
	
	modport master (
			output chip
		);
	
	modport slave (
			input chip
		);
	
endinterface

/**
 * Interface: dsi3_symbol_if
 * 
 * DSI3 interface containing a symbol
 */
interface dsi3_symbol_if;
	dsi3_pkg::dsi3_symbol symbol;
	
	modport master (
			output symbol
		);
	
	modport slave (
			input symbol
		);
	
endinterface

