/**
 * Module: ram_model
 *
 * TODO: Add module documentation
 */
module register_read_model import project_pkg::*; (
		clk_reset_if.slave	clk_rst,
		elip_full_if.slave	elip
	);

	`include "DW_ecc_function.inc"

	initial begin
		elip.data_read = '0;
		elip.ready = 1'b0;
	end

	always @ (negedge clk_rst.clk or posedge clk_rst.clk) begin
		if (clk_rst.clk == 1'b1) begin
			elip.ready <= 1'b0;
			elip.data_read <= '0;
		end
		else begin
			if (clk_rst.clk == 1'b0) begin
				if (elip.rd == 1'b1) begin
					elip.data_read <= get_random_data();
					elip.ready <= 1'b1;
				end
			end
			else begin
				elip.data_read.data <= '0;
				elip.data_read.ecc <= ECC_FOR_DATA_0;
				elip.ready <= 1'b0;
			end
		end
	end

	function automatic data_ecc_t get_random_data();
		data_ecc_t	data;
		data.data = $urandom_range('hffff,0);
		data.ecc = DWF_ecc_gen_chkbits(16,6,data.data);
		return data;
	endfunction

endmodule


