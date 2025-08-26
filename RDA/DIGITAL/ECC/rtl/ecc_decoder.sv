/**
 * Module: ecc_decoder
 *
 * scalable ecc decoder with Synopsys DW component
 */

module ecc_decoder import ECC_pkg::*; #(
		parameter DATA_WIDTH = 16,
		parameter int ECC_WIDTH  = 6
		) (
			input  logic                  i_correct_n,
			input  logic[DATA_WIDTH-1:0]  i_data,
			input  logic[ECC_WIDTH-1:0]   i_ecc,
			output logic[DATA_WIDTH-1:0]  o_data,
			output logic                  o_ecc_cor,
			output logic                  o_ecc_err
		);

		`ifndef target_technology_FPGA

		DW_ecc #(
				.width    (DATA_WIDTH),
				.chkbits  (ECC_WIDTH),
				.synd_sel (0)
			) i_ecc_dw_decoder (
				.gen        (i_correct_n),
				.correct_n  (i_correct_n),
				.datain     (i_data),
				.chkin      (i_ecc),
				.err_detect (o_ecc_cor),
				.err_multpl (o_ecc_err),
				.dataout    (o_data),
				.chkout     ()
			);

	`else

		assign o_data    = i_data;
		assign o_ecc_cor = 1'b0;
		assign o_ecc_err = 1'b0;

	`endif

endmodule