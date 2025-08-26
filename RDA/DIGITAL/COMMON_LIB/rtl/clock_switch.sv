/**
 * Module: clock_switch
 * 
 * Clock switch module for glitch free clock switching.
 * Default clock is i_clk1.
 * 
 */
module clock_switch (
		input	logic	i_clk1,
		input	logic	i_clk2,
		input	logic	i_sel_clk2,
		input	logic	i_rstn,
		input	logic	i_tst_en,
		input	logic	i_tst_sel,
		output	logic	o_clk,
		output	logic	o_clk_switched
	);
	
	logic clk1, clk2;
	logic sel_int;
	logic sel_1_s, sel_1_s_n;
	logic sel_2_s, sel_2_s_n;
	
	//*###   distribute internal signals   ######################################################*/
	
	// internal select signal
	assign	sel_int = (i_tst_en == 1'b0) ? i_sel_clk2 : i_tst_sel;

	//internal clk signals
	assign	clk1 = sel_2_s_n & i_clk1;
	assign	clk2 = sel_1_s_n & i_clk2;
	
	assign o_clk = clk1 | clk2;
	
	//*###   sync clk2 to negedge   ######################################################*/
	
	always_ff @(posedge i_clk2, negedge i_rstn) begin
		if (i_rstn == 1'b0) begin
			sel_1_s <= 1'b0;
		end
		else begin
			sel_1_s <= sel_int & ~sel_2_s_n;
		end
	end
	
	always_ff @(negedge i_clk2, negedge i_rstn) begin
		if (i_rstn == 1'b0) begin
			sel_1_s_n <= 1'b0;
		end 
		else begin
			sel_1_s_n <= sel_1_s;
		end
	end
	
	//*###   sync clk1 2 to negedge   ######################################################*/
	
	always_ff @(posedge i_clk1, negedge i_rstn) begin
		if (i_rstn == 1'b0) begin
			sel_2_s <= 1'b1;
		end
		else begin
			sel_2_s <= ~sel_int & ~sel_1_s_n;
		end
	end
	
	always_ff @(negedge i_clk1, negedge i_rstn) begin
		if (i_rstn == 1'b0) begin
			sel_2_s_n <= 1'b1;
		end
		else begin
			sel_2_s_n <= sel_2_s;
		end
	end
	
	assign	o_clk_switched = (sel_int == 1'b0) ? sel_2_s_n : sel_1_s_n;
	
endmodule


