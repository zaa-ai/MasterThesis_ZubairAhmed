/**
 * Module: spi_error_buffer
 * 
 * Buffer that stores error information regarding a specific transfer and releases those errors on transmission end
 */
module spi_error_buffer(
		clk_reset_if.slave clk_rst,
		input	logic	i_crc_error,
		input	logic	i_command_incomplete,
		input	logic	i_status_word_sent,
		output	logic	o_sce,
		output	logic	o_crc_error
	);
	
	logic[0:0]	crc_error_fifo, crc_error_fifo_next;
	logic[0:0]	sce_error_fifo, sce_error_fifo_next;
	
	logic	sce;
	assign	sce = /*i_undefined_command |*/ i_command_incomplete;
	
	always_ff@(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0) begin
			crc_error_fifo <= '0;
			sce_error_fifo <= '0;
		end
		else begin
			crc_error_fifo <= crc_error_fifo_next;
			sce_error_fifo <= sce_error_fifo_next;
		end
	end
	
	always_comb begin
		crc_error_fifo_next[0] = crc_error_fifo[0] | i_crc_error;
		if (i_status_word_sent == 1'b1) begin
			crc_error_fifo_next = i_crc_error;
		end
	end
	
	always_comb begin
		sce_error_fifo_next[0] = sce_error_fifo[0] | sce;
		if (i_status_word_sent == 1'b1) begin
			sce_error_fifo_next = sce;
		end
	end
	
	assign	o_crc_error = crc_error_fifo[0];
	assign	o_sce = sce_error_fifo[0];

endmodule
