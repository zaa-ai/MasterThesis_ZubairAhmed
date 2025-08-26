/**
 * Module: dsi3_chip_filter_counter
 * 
 * The DSI3 chip filer counter is used to count the number of clock cycles a chip is received that has another value than the filtered one
 * There is one counter for each of the possible chip values C0, C1 and C2
 * 
 *  As long as the value to observe by the counter equals the filtered one the counter is inactive (zero)
 *  If there is a difference between the observe and the filteres values the counter counts either upwards (input has the observe value) 
 *  or downwards. (Of course limited by the counter size.)
 *  
 */
module dsi3_chip_filter_counter import dsi3_pkg::*;  #(
		dsi3_chip   COUNT_VALUE					// the value to observe
	)(
		clk_reset_if.slave  			clk_rst,
		input   dsi3_chip   			i_input_value,       // the input value coming from the analog receiver
		input   dsi3_chip   			i_filtered_value,    // the value after the input filter (this counter belongs to)
		input	logic					i_shorter_filter_time,
		output  dsi3_filter_counter_t 	o_cnt
	);

	dsi3_filter_counter_t	 cnt_nxt, max_value;
	
	always_comb begin
		if (i_shorter_filter_time == 1'b1)
			max_value = 4'd10;
		else
			max_value = '1;
	end
	
	generate
		if (COUNT_VALUE == C1) begin : generate_filter_for_C1
			dsi3_chip	previous_filtered_value;
			
			always_comb begin
				cnt_nxt = o_cnt;
				if (COUNT_VALUE == i_filtered_value) begin
					cnt_nxt = '0;
				end
				else begin
					if (((((i_input_value == C0) && (i_filtered_value == C2)) || ((i_input_value == C2) && (i_filtered_value == C0)))) ||
							(i_input_value == COUNT_VALUE)) begin
						if (o_cnt < max_value) begin
							cnt_nxt = o_cnt + 4'd1;
						end
					end else begin
						if (o_cnt != 4'b0000) begin
							cnt_nxt = o_cnt - 4'd1;
						end
					end
				end
				if (i_filtered_value != previous_filtered_value) begin
					cnt_nxt = '0;
				end
			end
			
			always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
				if (clk_rst.rstn == 1'b0)  begin
					previous_filtered_value <= dsi3_pkg::C0;
				end else begin
					previous_filtered_value <= i_filtered_value;
				end
			end	
		end
		else begin : generate_filter_for_other_values
			always_comb begin
				cnt_nxt = o_cnt;
				if (COUNT_VALUE == i_filtered_value) begin
					cnt_nxt = '0;
				end
				else begin
					if (i_input_value == COUNT_VALUE) begin
						if (o_cnt < max_value) begin
							cnt_nxt = o_cnt + 4'd1;
						end
					end else begin
						if (o_cnt != 4'b0000) begin
							cnt_nxt = o_cnt - 4'd1;
						end
					end
				end
			end
		end
	endgenerate
	
	always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0)  begin
			o_cnt <= '0;
		end else begin
			o_cnt <= cnt_nxt;
		end
	end	

endmodule
