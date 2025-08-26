/**
 * Module: dsi3_receive_filter
 * 
 * filter for the received current chip
 */
module dsi3_receive_filter  import dsi3_pkg::*; (
		clk_reset_if.slave	clk,
		input	logic		filter_tick,
		dsi3_chip_if.slave 	dsi3_in,
		dsi3_chip_if.master dsi3_out,
		output	logic		chip_change,					// any change in Chip
		output	logic		chip_edge_from_0				// edge from C0 to C1 or C2 (initial edge)
	);
	
	logic [2:0]	cnt_nxt;
	dsi3_chip chip_buffer[2:0];
	dsi3_chip chip_buffer_nxt[2:0];
	dsi3_chip chip_filtered, chip_filtered_nxt;
	
	assign	dsi3_out.chip = chip_filtered;
	assign	chip_change = (chip_filtered != chip_filtered_nxt) ? 1'b1 : 1'b0;
	assign	chip_edge_from_0 = ((chip_filtered == C0) && ((chip_filtered_nxt == C1)||(chip_filtered_nxt == C2)));
	
	always_ff @(posedge clk.clk or negedge clk.rstn) begin
		if (clk.rstn == 1'b0)  begin
			foreach (chip_buffer[i]) begin
				chip_buffer[i] <= C0;
			end
			chip_filtered <= C0;
		end
		else begin
			if (filter_tick) begin
				chip_filtered	<= chip_filtered_nxt;
				chip_buffer		<= chip_buffer_nxt;
			end
		end
	end
	
	always_comb begin
		chip_buffer_nxt = {chip_buffer[1:0], dsi3_in.chip};
		cnt_nxt = 3'd0;
		for (int i=0; i<3; i++) begin
			case (chip_buffer_nxt[i])
				C0,C1,C2: begin
					cnt_nxt += chip_buffer_nxt[i];
				end
				default: begin
					cnt_nxt = cnt_nxt;
				end
			endcase
		end
	end
	
	always_comb begin
		case (cnt_nxt)
			3'd0: chip_filtered_nxt = C0;
			3'd3, 3'd2: chip_filtered_nxt = C1;
			3'd6, 3'd5: chip_filtered_nxt = C2;
			3'd1, 3'd4: chip_filtered_nxt = chip_filtered;
			default: begin
				chip_filtered_nxt = C0;
			end
		endcase
	end
	
endmodule


