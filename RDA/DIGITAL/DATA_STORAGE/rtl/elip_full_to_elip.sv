/**
 * Module: elip_full_to_elip
 *
 * converter from elip_full_if to elip_if
 */
module elip_full_to_elip import project_pkg::*; (
		elip_full_if.slave	elip_full,
		elip_if.master		elip,
		input	elip_data_t		i_data_read
	);

	/*###   ECC_ENCODER   ######################################################*/

	ecc_encoder #(
			.DATA_WIDTH (DATA_WIDTH),
			.ECC_WIDTH  (ECC_WIDTH)
		) i_ecc_enc_spi (
			.i_data     (i_data_read),
			.o_ecc      (elip_full.data_read.ecc)
		);

	assign	elip.addr		= elip_full.addr;
	assign	elip.wr			= elip_full.wr;
	assign	elip.rd			= elip_full.rd;
	assign	elip.data_write	= elip_full.data_write.data;

	assign	elip_full.ready	= 1'b1;
	assign	elip_full.data_read.data = i_data_read;

endmodule
