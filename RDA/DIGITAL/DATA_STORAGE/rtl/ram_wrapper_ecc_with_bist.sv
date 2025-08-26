/**
 * Module: ram_wrapper_ecc_with_bist
 *
 * module including a wrapper around the RAM and additional ECC logic as well as a BIST logic
 */
module ram_wrapper_ecc_with_bist import project_pkg::*;(
		clk_reset_if.slave	            clk_rst,
		elip_full_if.slave	            elip,
		jtag_bus_if.slave               jtag_bus,
		input  logic                    i_scan_mode,
		output logic [15:0]             o_jtag_dr,
		ecc_error_if.master				ecc_error
	);

	/*###   definitions   #########################################################*/
	import bist_pkg::*;

	logic       ecc_corr_1, ecc_corr_2;
	logic       ecc_fail_1, ecc_fail_2;

	bist_if bist ();
	logic                  		ce;
	data_t                 		sram_din_ecc_corrected;
	data_t                 		rdata;

	/*###   assign  ##############################################################*/
	assign ce   = elip.wr | elip.rd;

	/*###   ECC bus decoder input stage   ############################################*/
	ecc_decoder #(
			.DATA_WIDTH (DATA_WIDTH ),
			.ECC_WIDTH  (ECC_WIDTH  )
		) i_ecc_dec_1 (
			.i_correct_n(~elip.wr),
			.i_data     (elip.data_write.data),
			.i_ecc      (elip.data_write.ecc),
			.o_data     (sram_din_ecc_corrected),
			.o_ecc_cor  (ecc_corr_1),
			.o_ecc_err  (ecc_fail_1)
		);

	/*#####################################################################*/
	/*###    SRAM BIST section   ##########################################*/
	/*#####################################################################*/

	/*###    SRAM BIST test registers   ##########################################*/
	`include "SRAM_BIST_registers_if_inst.sv"
	clk_reset_if clk_rst_jtag ();

	assign  clk_rst_jtag.clk = jtag_bus.clk;
	assign  clk_rst_jtag.rstn = jtag_bus.rstn;
	
	ecc_t	ecc_to_be_tested;

	SRAM_BIST_registers #(
			.base_addr                   (BASE_ADDR_TEST_SRAM    ),
			.addr_width                  (JTAG_IR_WIDTH          )
		) i_SRAM_BIST_registers (
			.clk_rst                     (clk_rst_jtag.slave     ),
			.addr                        (jtag_bus.addr          ),
			.data_in                     (jtag_bus.data_write    ),
			.wr                          (jtag_bus.wr            ),
			.rd                          (jtag_bus.rd            ),
			.data_out                    (o_jtag_dr              ),
			.SRAM_BIST_registers_SRAM_ECC_CONTROL  (SRAM_BIST_registers_SRAM_ECC_CONTROL.master ), 
			.SRAM_BIST_registers_SRAM_BIST_CTRL (SRAM_BIST_registers_SRAM_BIST_CTRL.master),
            .SRAM_BIST_registers_SRAM_BIST_STAT (SRAM_BIST_registers_SRAM_BIST_STAT.master));
	
	/*###    connection to SRAM BIST module   ########################o##################*/
	assign	bist.run         = SRAM_BIST_registers_SRAM_BIST_CTRL.EN; //is synchronized to clk in utils_sram_bist_core
	assign	bist.bitwise     = SRAM_BIST_registers_SRAM_BIST_CTRL.BITWISE;
	assign	bist.four_6n     = SRAM_BIST_registers_SRAM_BIST_CTRL.FOUR_6N;    //
	assign	bist.parity_swap = SRAM_BIST_registers_SRAM_ECC_CONTROL.SRAM_ECC_SWAP;  // swap ecc bits with data bits
	assign	bist.ecc_val     = SRAM_BIST_registers_SRAM_ECC_CONTROL.SRAM_ECC_VAL;    //
	assign	bist.ecc_sel     = SRAM_BIST_registers_SRAM_ECC_CONTROL.SRAM_ECC_SEL;    //

	assign	SRAM_BIST_registers_SRAM_BIST_STAT.STATUS_in = bist.state;
	assign	SRAM_BIST_registers_SRAM_BIST_STAT.STATUS_set = 1'b1;

	/*###    SRAM BIST module   ##########################################*/
	utils_sram_with_bist #(
			.NUM_PARTS     (SRAM_NUM_PARTS   ),
			.DATA_WIDTH    (DATA_WIDTH       ),
			.ADDR_WIDTH    (SRAM_ADDR_WIDTH  ),
			.DEPTH         (SRAM_DEPTH       ),
			.WITH_PARITY   (SRAM_WITH_PARITY ),
			.WITH_ECC      (SRAM_WITH_ECC    ),
			.PROTECT_ADDR  (SRAM_PROTECT_ADDR),
			.MARCH_17N     (SRAM_MARCH_17N   )
		) utils_sram_with_bist_inst (
			.clk           (clk_rst.clk                    ),
			.nrst          (clk_rst.rstn                   ),
			.parity_event  (ecc_fail_2                     ),
			.corrected     (ecc_corr_2                     ),
			.bist          (bist.sp                        ),
			.ce            (ce                             ),
			.we            (elip.wr                        ),
			.oe            (elip.rd                        ),
			.addr          (elip.addr[SRAM_ADDR_WIDTH-1:0] ),
			.wdata         (sram_din_ecc_corrected         ),
			.rdata         (rdata                          ),
			.scan_mode     (i_scan_mode                    ));

	/*###   ECC bus encoder output stage #############################################*/
	ecc_encoder #(
			.DATA_WIDTH (DATA_WIDTH ),
			.ECC_WIDTH  (ECC_WIDTH  )
		) i_ecc_enc_2 (
			.i_data     (rdata),
			.o_ecc      (ecc_to_be_tested)
		);

	/*###   output assignments #############################################*/
	assign elip.data_read.ecc = SRAM_BIST_registers_SRAM_ECC_CONTROL.ELIP_ECC ^ ecc_to_be_tested;
	assign elip.data_read.data = rdata;
	assign elip.ready          = elip.rd | elip.wr;
	assign ecc_error.single_error = ecc_corr_1 | ecc_corr_2;
	assign ecc_error.double_error = ecc_fail_1 | ecc_fail_2;
endmodule
