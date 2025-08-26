/**
 * Module: buffer_writer_access_arbiter
 * 
 * arbiter for clearing and writing via buffer writer interface from 2 different sources
 */
module buffer_writer_access_arbiter(
		clk_reset_if.slave		clk_rst,
		input	logic	i_get_access_fsm,
		input	logic	i_get_access_clearing,
		output	logic	o_grant_access_fsm,
		output	logic	o_grant_access_clearing
	);
	
	logic	grant_access_fsm_next, grant_access_clearing_next;
	
	always_ff@(posedge clk_rst.clk or negedge clk_rst.rstn) begin // pad outputs should be FFs -> no glitches
		if (clk_rst.rstn == 1'b0) begin
			o_grant_access_fsm <= 1'b0;
			o_grant_access_clearing <= 1'b0;
		end
		else begin
			o_grant_access_fsm <= grant_access_fsm_next;
			o_grant_access_clearing <= grant_access_clearing_next;
		end
	end
	
	always_comb begin
		grant_access_clearing_next = o_grant_access_clearing;
		grant_access_fsm_next = o_grant_access_fsm;
		if (i_get_access_fsm == 1'b0) begin
			grant_access_fsm_next = 1'b0;
		end
		else begin
			if ((o_grant_access_clearing == 1'b0) && (i_get_access_clearing == 1'b0)) begin
				grant_access_fsm_next = 1'b1;
			end
		end
		if (i_get_access_clearing == 1'b0) begin
			grant_access_clearing_next = 1'b0;
		end
		else begin
			if ((o_grant_access_fsm == 1'b0) || (i_get_access_fsm == 1'b0)) begin
				grant_access_clearing_next = i_get_access_clearing;
			end
		end
	end

endmodule
