/**
 * Module: dsi3_crc_module
 * 
 * Module for DSI3 CRC calculation
 */
module dsi3_crc_parallel(
		input	logic[7:0]	i_seed,					// seed for CRC calculation
		input	logic[15:0]	i_data,					// input data
		output	logic[7:0]	o_crc					// calculated CRC
	);
	
	/*###   CRC calculation   ######################################################*/
	logic[7:0] crc[4:0];
	assign crc[4] = i_seed;
	
	generate
		genvar crc_stage;
		for (crc_stage=4; crc_stage>0; crc_stage--) begin : generate_crc_stages
			dsi3_crc_parallel_symbol i_dsi3_crc_parallel_symbol (
				.i_crc   (crc[crc_stage]  ), 
				.i_data  (i_data[((crc_stage)*4-1)-:4]), 
				.o_crc   (crc[crc_stage-1]  )
			);			
		end
	endgenerate
	assign	o_crc = crc[0];
	
endmodule


