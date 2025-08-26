/**
 * Module: ecc_encoder
 *
 * scalable ecc encoder with Synopsys DW component
 */

module ecc_encoder import ECC_pkg::*; #(
		parameter DATA_WIDTH = 16,
		parameter int ECC_WIDTH  = 6
		) (
			input  logic[DATA_WIDTH-1:0]  i_data,
			output logic[ECC_WIDTH-1:0]   o_ecc
		);

		`ifndef target_technology_FPGA

		DW_ecc #(
				.width    (DATA_WIDTH),
				.chkbits  (ECC_WIDTH),
				.synd_sel (0)
			) i_dw_ecc_encoder (
				.gen        (1'b1),
				.correct_n  (1'b1),
				.datain     (i_data),
				.chkin      (ECC_WIDTH'(0)),
				.err_detect (),
				.err_multpl (),
				.dataout    (),
				.chkout     (o_ecc)
			);

	`else

		assign o_ecc = '0;

	`endif

endmodule