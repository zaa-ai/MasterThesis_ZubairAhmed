/**
 * Module: dsi3_chip_converter
 * 
 * DSI3 module for converting the signals from the receiver to chips. Includes setting of chips, which do not exist.   
 */
module dsi3_chip_converter import dsi3_pkg::*; (
		input	logic[1:0]	receiver_output,
		dsi3_chip_if.master dsi3_chip_out
	);
	
	
	
	dsi3_chip	chip;
	
	assign	dsi3_chip_out.chip = chip;
	
	always_comb begin
		case (receiver_output)
			2'b00:		chip = C0;
			2'b01:		chip = C1;
			2'b11:		chip = C2;
			2'b10:		chip = CX;
			default: 	chip = C0;
		endcase
	end

endmodule


