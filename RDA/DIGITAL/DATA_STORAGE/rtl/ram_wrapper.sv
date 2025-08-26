/**
 * Module: ram_wrapper
 *
 * TODO: Add module documentation
 */
module ram_wrapper import project_pkg::*;(
		clk_reset_if.slave	clk_rst,
		elip_full_if.slave	elip
	);
	logic [22:0]	data_out;

	`ifdef target_technology_FPGA
		sram_3072x23 sram_3072_x23_inst (
				.clka  (~clk_rst.clk),               // input wire clka
				.wea   (elip.wr),                 // input wire [0 : 0] wea
				.addra (elip.addr[11:0]),           // input wire [11 : 0] addra
				.dina  ({7'd0, elip.data_write}),// input wire [22 : 0] dina
				.douta (data_out)                   // output wire [22 : 0] douta
			);

	`else
		//FIXME: add ECC with address + data
		SRAM_3072X23U18 i_SRAM_3072X23U18 (
				.Q    (data_out),
				.CLK  (~clk_rst.clk ),
				.CEN  (1'b0 ), 		//FIXME: set with IDDQ?
				.WEN  (~elip.wr ),
				.A    (elip.addr[11:0] ),
				.D    ({7'd0, elip.data_write}));

	`endif
	assign	elip.data_read = data_out[15:0];
	assign	elip.ready = elip.rd || elip.wr;
endmodule


