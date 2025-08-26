/****************************************************************************
 * IO_DIN_DIG.sv
 ****************************************************************************/

/**
 * Module: IO_DIN_DIG
 * 
 * Simple pad modell with positve logic input enable and pulldown and pullup capability
 * Inputs:
 * 	I - from digtial logic
 * 	OE - output enable high active
 * 	DS - drive strength (not used yet)
 * 	PU - pullup enable
 * 	PD - pulldown enable
 * 	IE - input enable
 * 	outputs:
 * 	C - to digital logic, depends on IE and PAD
 * 	AOUT - directly connected to PAD
 * 	inouts:
 * 	PAD - analogue Pad
 * 	Supply pins:
 * 	VDDPST, VDD, VSSPST, VSS
 * 		
 */
module IO_DIN_DIG (
		input  logic I, OE, DS, PU, PD, IE,
		input  logic VDDPST, VDD, VSSPST, VSS,
		output logic C,
		output wire  AOUT,
		inout PAD
		);

	// C
	logic C_int;
	buf(C_int, PAD);
	always_comb begin
		C    = IE ? C_int : VSS;
	end

	// PAD
	assign PAD = OE ? I : 1'bz;
	assign (pull1, highz0) PAD = PU ? 1'b1 : 1'bz;
	assign (highz1, pull0) PAD = PD ? 1'b0 : 1'bz;
	
	// AOUT
	assign AOUT = PAD;
	
endmodule


