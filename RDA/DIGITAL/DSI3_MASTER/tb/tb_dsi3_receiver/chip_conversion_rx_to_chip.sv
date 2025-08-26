/**
 * Module: chip_conversion_rx_to_chip
 * 
 * Converts RX signal to Chip representation
 */
module chip_conversion_rx_to_chip(
		input	logic [1:0] in,
		output	logic [1:0]	out
	);
	
	always_comb begin
		case (in)
			2	: out = 3;
			3	: out = 2;
			default: out = in;
		endcase
	end

endmodule
