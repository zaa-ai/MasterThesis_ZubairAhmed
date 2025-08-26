/**
 * Module: romnibble_instantiation
 * 
 * instantiate corresponding ROMNIBBLE cell by parameter
 * VALUE: ROMNIBBLE value
 */
module romnibble_instantiation#(
		parameter bit[3:0] VALUE
	)(	
		output	logic[3:0]	nibble_out
	);
	
	if (VALUE == 4'h0) begin: generate_rom_nibble_0 ROMNIBBLE_0 i_ROMNIBBLE_0 (.O (nibble_out)); end
	if (VALUE == 4'h1) begin: generate_rom_nibble_1 ROMNIBBLE_1 i_ROMNIBBLE_1 (.O (nibble_out)); end
	if (VALUE == 4'h2) begin: generate_rom_nibble_2 ROMNIBBLE_2 i_ROMNIBBLE_2 (.O (nibble_out)); end
	if (VALUE == 4'h3) begin: generate_rom_nibble_3 ROMNIBBLE_3 i_ROMNIBBLE_3 (.O (nibble_out)); end
	if (VALUE == 4'h4) begin: generate_rom_nibble_4 ROMNIBBLE_4 i_ROMNIBBLE_4 (.O (nibble_out)); end
	if (VALUE == 4'h5) begin: generate_rom_nibble_5 ROMNIBBLE_5 i_ROMNIBBLE_5 (.O (nibble_out)); end
	if (VALUE == 4'h6) begin: generate_rom_nibble_6 ROMNIBBLE_6 i_ROMNIBBLE_6 (.O (nibble_out)); end
	if (VALUE == 4'h7) begin: generate_rom_nibble_7 ROMNIBBLE_7 i_ROMNIBBLE_7 (.O (nibble_out)); end
	if (VALUE == 4'h8) begin: generate_rom_nibble_8 ROMNIBBLE_8 i_ROMNIBBLE_8 (.O (nibble_out)); end
	if (VALUE == 4'h9) begin: generate_rom_nibble_9 ROMNIBBLE_9 i_ROMNIBBLE_9 (.O (nibble_out)); end
	if (VALUE == 4'hA) begin: generate_rom_nibble_A ROMNIBBLE_A i_ROMNIBBLE_A (.O (nibble_out)); end
	if (VALUE == 4'hB) begin: generate_rom_nibble_B ROMNIBBLE_B i_ROMNIBBLE_B (.O (nibble_out)); end
	if (VALUE == 4'hC) begin: generate_rom_nibble_C ROMNIBBLE_C i_ROMNIBBLE_C (.O (nibble_out)); end
	if (VALUE == 4'hD) begin: generate_rom_nibble_D ROMNIBBLE_D i_ROMNIBBLE_D (.O (nibble_out)); end
	if (VALUE == 4'hE) begin: generate_rom_nibble_E ROMNIBBLE_E i_ROMNIBBLE_E (.O (nibble_out)); end
	if (VALUE == 4'hF) begin: generate_rom_nibble_F ROMNIBBLE_F i_ROMNIBBLE_F (.O (nibble_out)); end
endmodule
