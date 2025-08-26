//`include "DW_ecc_function.inc"
/**
 * Module: ecc_register
 *
 * scalable register with ecc protection
 */
module ecc_register import ECC_pkg::*; #(
		parameter WIDTH    = 16,
		parameter RESET_VAL = 0
		) (
			clk_reset_if.slave      clk_rst,
			input  logic            i_waccess,
			input  logic            i_raccess,
			input  logic[WIDTH-1:0] i_wdata,
			output logic[WIDTH-1:0] o_rdata,
			output logic            o_ecc_corr,
			output logic            o_ecc_fail
		);

		/*###   defintions / functions   ###########################################*/
	typedef logic [WIDTH-1:0] data_reg_t;
	data_reg_t data_reg;

	generate
		if (WIDTH > 7) begin : WIDTH_greater_7
			typedef logic [get_ecc_width(WIDTH)-1:0] ecc_t;
			ecc_t ecc_reg, ecc;

			/*###   ecc and data_reg register     ############################################*/
			always_ff@(posedge clk_rst.clk or negedge clk_rst.rstn) begin
				if (clk_rst.rstn == 1'b0) begin
					data_reg <= data_reg_t'(RESET_VAL);
					// @SuppressProblem -type argument_connection_extend_const_non_explicit_size -length 1 
					ecc_reg  <= ecc_t'(DWF_ecc_gen_chkbits(WIDTH, get_ecc_width(WIDTH), RESET_VAL));
				end
				else begin
					if (i_waccess == 1'b1) begin
						data_reg <= i_wdata;
						ecc_reg  <= ecc;
					end
				end
			end

			/*###   ecc encoder     ######################################################*/
			ecc_encoder #(
					.DATA_WIDTH (WIDTH),
					.ECC_WIDTH  (get_ecc_width(WIDTH))
				) i_ecc_encoder (
					.i_data     (i_wdata),
					.o_ecc      (ecc)
				);

			/*###   ecc deccoder     ######################################################*/
			ecc_decoder #(
					.DATA_WIDTH (WIDTH),
					.ECC_WIDTH  (get_ecc_width(WIDTH))
				) i_ecc_decoder (
					.i_correct_n(~i_raccess),
					.i_data     (data_reg),
					.i_ecc      (ecc_reg),
					.o_data     (o_rdata),
					.o_ecc_cor  (o_ecc_corr),
					.o_ecc_err  (o_ecc_fail)
				);
		end
		else begin  : WIDTH_less_8
			typedef logic [get_ecc_width(8)-1:0] ecc_t;
			ecc_t ecc_reg, ecc;

			logic [7:0] din_ecc_encoder;
			logic [7:0] din_ecc_decoder;
			// @SuppressProblem -type partially_unread_data -count 1 -length 1
			logic [7:0] data_reg_corrected;
			
			assign	din_ecc_encoder[7:WIDTH] = '0;
			assign	din_ecc_encoder[WIDTH-1:0] = i_wdata;

			/*###   ecc and data_reg register     ############################################*/
			always_ff@(posedge clk_rst.clk or negedge clk_rst.rstn) begin
				if (clk_rst.rstn == 1'b0) begin
					data_reg <= data_reg_t'(RESET_VAL);
					// @SuppressProblem -type argument_connection_extend_const_non_explicit_size -count 1 -length 1
					ecc_reg  <= ecc_t'(DWF_ecc_gen_chkbits(WIDTH, get_ecc_width(WIDTH), RESET_VAL));
				end
				else begin
					if (i_waccess == 1'b1) begin
						data_reg <= i_wdata;
						ecc_reg  <= ecc;
					end
				end
			end
			
			assign	din_ecc_decoder[7:WIDTH] = '0;
			assign	din_ecc_decoder[WIDTH-1:0] = data_reg;

			/*###   ecc encoder     ######################################################*/
			ecc_encoder #(
					.DATA_WIDTH (8),
					.ECC_WIDTH  (get_ecc_width(8))
				) i_ecc_encoder (
					.i_data     (din_ecc_encoder),
					.o_ecc      (ecc)
				);

			/*###   ecc deccoder     ######################################################*/
			ecc_decoder #(
					.DATA_WIDTH (8),
					.ECC_WIDTH  (get_ecc_width(8))
				) i_ecc_decoder (
					.i_correct_n(~i_raccess),
					.i_data     (din_ecc_decoder),
					.i_ecc      (ecc_reg),
					.o_data     (data_reg_corrected),
					.o_ecc_cor  (o_ecc_corr),
					.o_ecc_err  (o_ecc_fail)
				);

			assign o_rdata = data_reg_corrected[WIDTH-1:0];

		end
	endgenerate

endmodule
