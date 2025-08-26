/**
 * Module: ic_revision
 * 
 * module containing IC_REVISION
 */
module ic_revision import project_pkg::*;  (
		output	data_t	o_ic_revision
	);
	
	`include "svn_revision_inc.sv"
	
	parameter shortint REVISION = `SVN_REVISION ;
	
//	generate
//		genvar i;
//		for (i=3; i<16; i+=4) begin : generate_nibbles
//			ROMNIBBLE #(
//					.VALUE (IC_REVISION[i-:4])
//				) i_ROMNIBBLE (
//					.out (o_ic_revision[i-:4])
//				);
//		end
//	endgenerate
	
	romnibble_instantiation #(.VALUE (REVISION[ 3: 0])) i_ROMNIBBLE_3_0   (.nibble_out (o_ic_revision[ 3: 0]));
	romnibble_instantiation #(.VALUE (REVISION[ 7: 4])) i_ROMNIBBLE_7_4   (.nibble_out (o_ic_revision[ 7: 4]));
	romnibble_instantiation #(.VALUE (REVISION[11: 8])) i_ROMNIBBLE_11_8  (.nibble_out (o_ic_revision[11: 8]));
	romnibble_instantiation #(.VALUE (REVISION[15:12])) i_ROMNIBBLE_15_12 (.nibble_out (o_ic_revision[15:12]));
	
endmodule
