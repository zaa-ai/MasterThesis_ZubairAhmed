/**
 * Module: dsi3_crc_parallel_symbol
 * 
 * Module for a pure combinational calculation of a CRC in a DSI3 system for a symbol (4 bit data input)
 */
module dsi3_crc_parallel_symbol(
		input logic[7:0]	i_crc,
		input logic[3:0]	i_data,
		output logic[7:0]	o_crc
	);
	
	
	always@(i_crc, i_data) begin
		logic[7:0] crc_in, crc_out;
		crc_in = i_crc;
		for (int i=3; i>=0; i--) begin
			calc_crc(i_data[i], crc_in, crc_out);
			crc_in = crc_out;
		end
		o_crc = crc_in;
	end	
	
	task calc_crc(input logic data_in, input logic[7:0] crc_in, output logic[7:0] crc_out);
		crc_out[0] = data_in ^ crc_in[7];
		crc_out[1] = crc_in[0] ^ crc_in[7];
		crc_out[2] = crc_in[1] ^ crc_in[7];
		crc_out[3] = crc_in[2] ^ crc_in[7];
		crc_out[4] = crc_in[3];
		crc_out[5] = crc_in[4] ^ crc_in[7];
		crc_out[6] = crc_in[5];
		crc_out[7] = crc_in[6];
	endtask	

endmodule


