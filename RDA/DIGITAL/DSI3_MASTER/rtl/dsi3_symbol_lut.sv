/**
 * Module: dsi3_symbol_lut
 * 
 * DSI3 symbol lookup table and error detection
 */
module dsi3_symbol_lut_module import dsi3_pkg::*; (
		input 	dsi3_symbol	symbol_in,				// input symbol
		output	logic [3:0] symbol_out,				// output data
		output	logic		error_invalid_chip,		// error flag, if an invalid chip (='11') was detected 
		output	logic		error_invalid_symbol	// error flag, if an invalid symbol was detected
	);

	always_comb begin
		if ((symbol_in[0] == CX) || (symbol_in[1] == CX) || (symbol_in[2] == CX))
			error_invalid_chip = 1'b1;
		else
			error_invalid_chip = 1'b0;
	end
	
	always_comb begin
		error_invalid_symbol = 1'b0;
		case (symbol_in)
			dsi3_symbol'({C1, C1, C0}):	symbol_out=4'h0;
			dsi3_symbol'({C2, C1, C1}):	symbol_out=4'h1;
			dsi3_symbol'({C1, C0, C2}):	symbol_out=4'h2;
			dsi3_symbol'({C2, C0, C2}):	symbol_out=4'h3;
			dsi3_symbol'({C1, C0, C0}):	symbol_out=4'h4;
			dsi3_symbol'({C2, C1, C2}):	symbol_out=4'h5;
			dsi3_symbol'({C1, C1, C2}):	symbol_out=4'h6;
			dsi3_symbol'({C2, C0, C1}):	symbol_out=4'h7;
			dsi3_symbol'({C2, C2, C0}):	symbol_out=4'h8;
			dsi3_symbol'({C2, C1, C0}):	symbol_out=4'h9;
			dsi3_symbol'({C1, C2, C2}):	symbol_out=4'ha;
			dsi3_symbol'({C2, C2, C1}):	symbol_out=4'hb;
			dsi3_symbol'({C1, C2, C0}):	symbol_out=4'hc;
			dsi3_symbol'({C2, C0, C0}):	symbol_out=4'hd;
			dsi3_symbol'({C1, C0, C1}):	symbol_out=4'he;
			dsi3_symbol'({C1, C2, C1}):	symbol_out=4'hf;
			default: begin
				symbol_out = 4'h0;
				error_invalid_symbol = 1'b1;
			end
		endcase
	end


endmodule


