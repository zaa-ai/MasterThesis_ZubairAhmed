/**
 * Module: sync_edge
 * 
 * synchronizer with edge detection for each bit
 */
module sync_edge #(
		parameter SIZE=1,
		parameter EDGE=0,
		parameter longint unsigned RESET_VALUE=0
	)(
		clk_reset_if.slave			clk_rst,
		input	logic [SIZE-1:0]	i_in,
		output	logic [SIZE-1:0]	o_test_out,
		output	logic [SIZE-1:0]	o_out,
		output	logic [SIZE-1:0]	o_rising,
		output	logic [SIZE-1:0]	o_falling
	);
	
	typedef logic [SIZE-1:0] sync_edge_t;
	
	logic [SIZE-1:0]	prev;
	
	always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0)  begin
			o_test_out	<= sync_edge_t'(RESET_VALUE);
			o_out		<= sync_edge_t'(RESET_VALUE);
		end
		else begin
			o_test_out	<= i_in;
			o_out		<= o_test_out;
		end
	end
	
	if (EDGE) begin : generate_edge_detection_ffs
		always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
			if (clk_rst.rstn == 1'b0)  begin
				prev		<= '0;
			end
			else begin
				prev		<= o_out;
			end
		end
	end
	else begin : generate_no_edge_detection_ffs
		assign prev = '0;
	end
	
	
	assign	o_rising = (EDGE) ? ~prev & o_out : '0;
	assign	o_falling = (EDGE) ? prev & ~o_out : '0;
		
endmodule


