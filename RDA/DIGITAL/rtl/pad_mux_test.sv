/**
 * Module: pad_mux_test
 * 
 * module for muxing pad control signals for all other pins 
 */
module pad_mux_test import project_pkg::*; (
		clk_reset_if.slave  clk_rst,
		pad_int_if.master	pad_out,
		pad_int_if.slave	pad_appl,
		input	logic					i_enable_input,
		input	logic					i_test_en,		// enable test output
		input	tmr_out_test_sel_t 		i_test_sel,		// select signal of output
		input	tmr_out_test_vector_t	i_test_vector,	// test vector
		output	logic 					o_test_out		// only for test coverage
	);
	
	// input signals
	assign	pad_appl.in_a = pad_out.in_a;
	assign	pad_out.ie = (i_enable_input == 1'b0) ? pad_appl.ie : 1'b1;
	
	assign	pad_out.oe = (i_test_en == 1'b1) ? 1'b1 : pad_appl.oe;
	assign	pad_out.pd = (i_test_en == 1'b1) ? 1'b0 : pad_appl.pd;
	assign	pad_out.pu = (i_test_en == 1'b1) ? 1'b0 : pad_appl.pu;
	
	always_comb begin
		pad_out.out = pad_appl.out;
		if (i_test_en == 1'b1) begin
			if (int'(i_test_sel) < TMR_OUT_TEST_VECTOR_WIDTH) begin
				pad_out.out = i_test_vector[i_test_sel];
			end
		end
	end
	
	logic test_reg, test_reg_nxt;
	
	always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0)  begin
			test_reg<= 1'b0;
		end
		else begin
			test_reg<= test_reg_nxt;
		end
	end
	
	assign test_reg_nxt = pad_out.oe ^ pad_out.out ^ pad_out.pd ^ pad_out.pu;
	assign o_test_out = test_reg;	
	
endmodule
