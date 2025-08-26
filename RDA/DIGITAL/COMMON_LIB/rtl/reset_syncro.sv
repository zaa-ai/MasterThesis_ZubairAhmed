/**
 * reset_syncro.sv by STRI, 10 2017
 */


module reset_syncro(
	input  logic i_clk,
	input  logic i_clkn,
	input  logic i_resn,
	input  logic i_atpgmode,
	output logic o_clkn_resn,
	output logic o_clk_resn

);

logic resn_sync_re;
logic resn_sync_fe;
logic resn_sync_internal; 

always_ff @(posedge i_clk or negedge i_resn) begin
	if (!i_resn)  begin
		resn_sync_internal <= 1'b0;
		resn_sync_fe <= 1'b0;
	end
	else begin
		resn_sync_internal <= i_resn;
		resn_sync_fe <= resn_sync_re;
	end
end

always_ff @(posedge i_clkn or negedge i_resn) begin
	if (!i_resn)  begin
		resn_sync_re <= 1'b0;
	end
	else begin
		resn_sync_re <= resn_sync_internal;
	end
end

assign o_clk_resn  = (i_atpgmode == 1'b0) ? resn_sync_re : i_resn;
assign o_clkn_resn = (i_atpgmode == 1'b0) ? resn_sync_fe : i_resn;

endmodule
