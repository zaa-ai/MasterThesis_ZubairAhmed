/**
 * Module: ram_model
 * 
 * Model replacing a RAM in test cases
 */
module ram_model import project_pkg::*; #(
		parameter RAM_SIZE = 6144,
		parameter OFFSET = 0
	)(
		clk_reset_if.slave	clk_rst,
		elip_full_if.slave	elip
	);
	
	data_ecc_t mem[RAM_SIZE-1:0];
	
	initial begin
		elip.data_read = '0;
		elip.ready = 1'b0;
	end
	
	always @ (negedge clk_rst.rstn or edge clk_rst.clk) begin
		if (clk_rst.rstn == 1'b0) begin
			elip.ready <= 1'b0;
			for (int i = 0; i < RAM_SIZE; i++) begin
				mem[i].data	<= '0;
				mem[i].ecc	<= ECC_FOR_DATA_0;
			end
		end
		else begin
			if (clk_rst.clk == 1'b1) begin
				elip.ready <= 1'b0;
			end
			else begin
				if (elip.rd == 1'b1) begin
					elip.data_read <= mem[elip.addr-OFFSET];
					elip.ready <= 1'b1;
				end
				if (elip.wr == 1'b1) begin
					elip.data_read <= elip.data_write;
					mem[elip.addr-OFFSET] <= elip.data_write;
					elip.ready <= 1'b1;
				end
			end
		end
	end
	
endmodule


