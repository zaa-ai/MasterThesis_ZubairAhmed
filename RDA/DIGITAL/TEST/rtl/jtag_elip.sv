/**
 * Module: jtag_elip
 * 
 * module for accessing ELIP bus via JTAG instructions
 */
module jtag_elip import project_pkg::*; (
		clk_reset_if.slave		clk_rst,
		clk_reset_if.slave		jtag_clk_rst,
		jtag_status_if.slave	status,
		elip_full_if.master		elip,
		output	jtag_dr_t		o_data_shift_register
	);
	
	logic	ir_is_read, ir_is_write;
	logic	ir_is_incremental, ir_is_full;
	
	logic	ir_read_full, ir_read_incremental, ir_read;
	logic	ir_write_full, ir_write_incremental, ir_write;
	
	elip_addr_t	address;
	data_ecc_t	data_write;
	data_t		data_read;
	
	ecc_t	ecc_for_write;
	
	ecc_encoder #(
		.DATA_WIDTH  (DATA_WIDTH ), 
		.ECC_WIDTH   (ECC_WIDTH  )
		) i_ecc_encoder (
		.i_data      (status.dsr[15:0]     ), 
		.o_ecc       (ecc_for_write      ));
	
	/*###   JTAG   ######################################################*/
	always_ff@(negedge jtag_clk_rst.clk or negedge jtag_clk_rst.rstn) begin
		if (jtag_clk_rst.rstn == 1'b0)  begin
			address	<= '0;
			data_write.data <= '0;
			data_write.ecc <= ECC_FOR_DATA_0;
		end
		else begin
			if (status.update_dr == 1'b1) begin
				if (ir_is_incremental == 1'b1) begin
					address <= address + elip_addr_t'(1);
				end
				if (ir_is_full == 1'b1) begin
					address	<= status.dsr[31:16];
				end
				if (ir_is_write == 1'b1) begin
					data_write.data <= status.dsr[15:0];
					data_write.ecc  <= ecc_for_write;
				end
			end
		end
	end
	
	assign	ir_is_read = ir_read | ir_read_full | ir_read_incremental;
	assign	ir_is_write = ir_write | ir_write_full | ir_write_incremental;
	assign	ir_is_incremental = ir_read_incremental | ir_write_incremental;
	assign	ir_is_full = ir_read_full | ir_write_full;

	always_comb begin
		ir_read_full = 1'b0;
		ir_read_incremental = 1'b0;
		ir_read = 1'b0;
		ir_write_full = 1'b0;
		ir_write_incremental = 1'b0;
		ir_write = 1'b0;
		
		case (status.ir)
			8'hc0:	ir_read_full = 1'b1;
			8'hc1:	ir_read = 1'b1;
			8'hc2:	ir_read_incremental = 1'b1;
			8'hc3:	ir_write_full = 1'b1;
			8'hc4:	ir_write = 1'b1;
			8'hc5:	ir_write_incremental = 1'b1;
		endcase
	end
	
	always_comb begin
		if ((ir_is_read | ir_is_write) == 1'b1) begin
			o_data_shift_register = {address , data_read};
		end
		else begin
			o_data_shift_register = '0;
		end
	end
	
	/*###   sync   ######################################################*/
	logic [2:0] update_dr_synced;
	logic	update;
	
	always_ff@(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0)  begin
			update_dr_synced[2:1]	<= '0;
		end
		else begin
			update_dr_synced[2:1]	<= update_dr_synced[1:0];
		end
	end
	always_ff@(negedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0)  begin
			update_dr_synced[0]	<= '0;
		end
		else begin
			update_dr_synced[0]	<= status.update_dr_fe;
		end
	end
	assign	update = update_dr_synced[2] & ~update_dr_synced[1];
	
	/*###   ELIP   ######################################################*/
	assign	elip.addr = address;
	assign	elip.data_write = data_write;
	assign	elip.rd = ir_is_read & update;
	assign	elip.wr = ir_is_write & update;
	
	always_ff@(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0)  begin
			data_read	<= '0;
		end
		else begin
			if (elip.ready == 1'b1)
				data_read	<= elip.data_read.data;
		end
	end

endmodule
