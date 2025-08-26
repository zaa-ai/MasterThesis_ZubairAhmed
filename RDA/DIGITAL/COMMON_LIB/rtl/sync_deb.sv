/**
 * Module: sync_deb
 * 
 * Module for synchronization and debouncing of a signal
 * 
 * RESET_VALUE: reset value of the signal after power-on-reset
 * DEBOUNCE_TIME: amount of clock cycles
 */
module sync_deb #(
		parameter DEBOUNCE_TIME = 15,
		parameter RESET_VALUE = 1'b0
		)(
		//interfaces
		clk_reset_if.slave clk_rst,
		//inputs
		input logic i_in,
		//outputs
		output logic o_out,
		output logic o_test_out
		);

	logic signal_i_s;
	//syncronizing stage
	sync #(
			.SIZE        ( 1 )
		) i_sync (
			.clk_rst     (clk_rst    ), 
			.i_in        (i_in		 ), 
			.o_test_out  (o_test_out ), 
			.o_out       (signal_i_s ));
	
	//debouncer
	deb #(
			.DEBOUNCE_TIME    (DEBOUNCE_TIME   ), 
			.RESET_VALUE      (RESET_VALUE     )
		) i_deb (
			.clk_rst          (clk_rst         ), 
			.i_in             (signal_i_s      ), 
			.o_out            (o_out           ));
endmodule
