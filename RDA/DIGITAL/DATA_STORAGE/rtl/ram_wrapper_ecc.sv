/**
 * Module: ram_wrapper_ecc
 *
 * TODO: Add module documentation
 */
module ram_wrapper_ecc import project_pkg::*;(
		clk_reset_if.slave	    clk_rst,
		elip_full_if.slave	    elip,
		output logic            o_ecc_fail
	);

	/*###   definitions   #########################################################*/
	localparam  SRAM_WIDTH      = 23;
	localparam  SRAM_ADDR_WIDTH = 12;
	localparam  SRAM_ECC_WIDTH  = 7;

	localparam  ELIP_DATA_WIDTH = 16;
	localparam  ELIP_ECC_WIDTH  = 6;

	logic       ecc_fail_1;
	logic       ecc_fail_2;

	logic[SRAM_WIDTH-1:0]                      sram_din;
	logic[SRAM_WIDTH-1:0]                      sram_dout;
	logic[SRAM_ADDR_WIDTH-1:0]                 sram_addr;

	logic[SRAM_ECC_WIDTH-1:0]                  sram_din_ecc;
	logic[ELIP_DATA_WIDTH-1:0]                 sram_din_ecc_corrected;
	logic[SRAM_ADDR_WIDTH+ELIP_DATA_WIDTH-1:0] sram_din_ecc_encoder;

	logic[SRAM_ECC_WIDTH-1:0]                  sram_dout_ecc;
	logic[SRAM_ADDR_WIDTH+ELIP_DATA_WIDTH-1:0] sram_dout_ecc_decoder;
	logic[SRAM_ADDR_WIDTH+ELIP_DATA_WIDTH-1:0] sram_dout_ecc_corrected;

	logic[ELIP_DATA_WIDTH-1:0]                 elip_dout;
	logic[ELIP_ECC_WIDTH-1:0]                  elip_dout_ecc;

	/*###   assign  ##############################################################*/

	assign sram_addr           = elip.addr[SRAM_ADDR_WIDTH-1:0];
	assign elip.data_read.data = elip_dout;
	assign elip.data_read.ecc  = elip_dout_ecc;
	assign elip.ready          = elip.rd || elip.wr;
	assign o_ecc_fail          = ecc_fail_1 || ecc_fail_2;

	/*###   ECC encoder input stage ##############################################*/

	assign sram_din_ecc_encoder = {sram_addr, sram_din_ecc_corrected};

	ecc_encoder #(
			.DATA_WIDTH (SRAM_ADDR_WIDTH+ELIP_DATA_WIDTH),
			.ECC_WIDTH  (SRAM_ECC_WIDTH)
		) i_ecc_enc_1 (
			.i_data     (sram_din_ecc_encoder),
			.o_ecc      (sram_din_ecc)
		);

	assign sram_din = {sram_din_ecc, sram_din_ecc_corrected};

	/*###   ECC encoder output stage #############################################*/

	assign elip_dout = sram_dout_ecc_corrected[ELIP_DATA_WIDTH-1:0];

	ecc_encoder #(
			.DATA_WIDTH (ELIP_DATA_WIDTH),
			.ECC_WIDTH  (ELIP_ECC_WIDTH)
		) i_ecc_enc_2 (
			.i_data     (elip_dout),
			.o_ecc      (elip_dout_ecc)
		);

	/*###   ECC decoder input stage   ############################################*/

	ecc_decoder #(
			.DATA_WIDTH (ELIP_DATA_WIDTH),
			.ECC_WIDTH  (ELIP_ECC_WIDTH)
		) i_ecc_dec_1 (
			.i_correct_n(~elip.wr),
			.i_data     (elip.data_write.data),
			.i_ecc      (elip.data_write.ecc),
			.o_data     (sram_din_ecc_corrected),
			.o_ecc_err  (ecc_fail_1)
		);

	/*###    ECC decoder output stage   ##########################################*/

	assign sram_dout_ecc_decoder = {sram_addr, sram_dout[ELIP_DATA_WIDTH-1:0]};
	assign sram_dout_ecc = sram_dout[SRAM_WIDTH-1:SRAM_WIDTH-SRAM_ECC_WIDTH];

	ecc_decoder #(
			.DATA_WIDTH (SRAM_ADDR_WIDTH+ELIP_DATA_WIDTH),
			.ECC_WIDTH  (SRAM_ECC_WIDTH)
		) i_ecc_dec_2 (
			.i_correct_n(~elip.rd),
			.i_data     (sram_dout_ecc_decoder),
			.i_ecc      (sram_dout_ecc),
			.o_data     (sram_dout_ecc_corrected),
			.o_ecc_err  (ecc_fail_2)
		);

	`ifdef target_technology_FPGA

		sram_3072x23 sram_3072_x23_inst (
				.clka  (~clk_rst.clk),
				.wea   (elip.wr),
				.addra (sram_addr),
				.dina  (sram_din),
				.douta (sram_dout)
			);

	`else

		SRAM_3072X23U18 i_SRAM_3072X23U18 (
				.Q    (sram_dout),
				.CLK  (~clk_rst.clk),
				.CEN  (1'b0), 		//FIXME: set with IDDQ?
				.WEN  (~elip.wr),
				.A    (sram_addr),
				.D    (sram_din)
			);

	`endif

endmodule


