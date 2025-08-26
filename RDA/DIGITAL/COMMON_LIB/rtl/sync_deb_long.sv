/**
 * Module: sync_deb_long
 * 
 * Module for synchronization and longer debouncing of a signal
 * 
 * RESET_VALUE: reset value of the signal after power-on-reset
 * DEBOUNCE_TIME: amount of ticks for debouncing
 */
module sync_deb_long #(
		parameter DEBOUNCE_TIME = 15,
		parameter RESET_VALUE = 1'b0
		)(
		//interfaces
		clk_reset_if.slave clk_rst,
		//inputs
		input logic i_in,
		input logic i_debounce_tick,
		//outputs
		output logic o_out,
		output logic o_test_out,
		output	logic	o_out_synced
	);

	//syncronizing stage
	sync #(
			.SIZE        ( 1 )
		) i_sync (
			.clk_rst     (clk_rst    ), 
			.i_in        (i_in		 ), 
			.o_test_out  (o_test_out ), 
			.o_out       (o_out_synced ));
	
	//debouncer
	deb_long #(
			.DEBOUNCE_TIME    (DEBOUNCE_TIME   ), 
			.RESET_VALUE      (RESET_VALUE     )
		) i_deb_long (
			.clk_rst          (clk_rst         ), 
			.i_in             (o_out_synced      ), 
			.i_debounce_tick  (i_debounce_tick ), 
			.o_out            (o_out           ));
endmodule


