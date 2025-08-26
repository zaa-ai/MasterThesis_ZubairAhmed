
`timescale 1ns/1ns

interface bist_if;
	import bist_pkg::*;

	logic       parity_swap;
	logic       run;
	logic       bitwise;
	logic       four_6n;
	bist_status_t state;
	logic       ecc_sel;
	logic [6:0] ecc_val;  // depending on the particular number of ECC or parity
	// bits, only the LSBs of ecc_val are used

	modport mp(
			output parity_swap,
			output run,
			output bitwise,
			output four_6n,
			input  state,
			output ecc_sel,
			output ecc_val
		);

	modport sp(
			input  parity_swap,
			input  run,
			input  bitwise,
			input  four_6n,
			output state,
			input  ecc_sel,
			input  ecc_val
		);

endinterface

