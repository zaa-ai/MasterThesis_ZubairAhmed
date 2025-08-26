/**
 * Module: control_command_buffer_clearing
 * 
 * module for controlling clearing of command control buffer
 */
module control_command_buffer_clearing import project_pkg::*;(
		clk_reset_if.slave		clk_rst,
		input	dsi_logic_t		i_dsi3_enabled,
		input	dsi_logic_t		i_cleared_command_buffer,
		input	dsi_logic_t		i_clear_command_buffer,
		output	dsi_logic_t		o_clear_command_buffer
	);
	
	dsi_logic_t	prev_enable, clear_posedge;
	dsi_logic_t	clear_command_buffer_next;
	
	assign	clear_posedge = prev_enable & ~i_dsi3_enabled; // clear when enable goes low
	
	always_comb begin
		for (int i=0; i< DSI_CHANNELS; i++) begin
			if (i_cleared_command_buffer[i] == 1'b1) begin // reset when cleared
				clear_command_buffer_next[i] = 1'b0;
			end
			else begin // set when disabled
				clear_command_buffer_next[i] = o_clear_command_buffer[i] | clear_posedge[i] | i_clear_command_buffer[i];
			end
		end
	end
	
	always_ff@(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0) begin
			prev_enable <= '0;
			o_clear_command_buffer <= '0;
		end
		else begin
			prev_enable <= i_dsi3_enabled;
			o_clear_command_buffer <= clear_command_buffer_next;
		end
	end

endmodule


