/**
 * Module: dsi3_receive
 *
 * Module for receiving dsi3 slave transmissions at the master
 */
module dsi3_receive import dsi3_pkg::*; import project_pkg::*;(
		clk_reset_if.slave  clk_rst,			// clock / reset interface
		input	logic		i_enable_receiver,	// enable receiver logic
		input	logic[1:0]	i_rx,			// DSI3 current comparator input (MSB=higher current, LSB=lower current)
		input	logic[1:0]	i_sample_cfg,		// Configuration of the chip time (0=3µs, 1=4µs, 2=5µs, ...)
		input	logic		i_receive_time_out,

		output	logic		o_rec_pending,		// receiving pending
		output	logic		o_received_data,
		output	logic		o_symbol_error_set,
		output	logic		o_response_finished,
		output	data_ecc_t  o_data,
		output	logic[1:0]	o_rx_test,
		output	logic[1:0]	o_rx_filtered,
		output	logic[8:0]	o_symbol_count,
		output	logic		o_symbol_count_overflow,
		output	logic		o_receiving_started_tick,
		output	logic		o_received_c0_after_packet
	);

	dsi3_chip_if chip_filtered();
	dsi3_chip_if chip_sampled();
	
	/*###   sync + filter   ######################################################*/
	dsi3_filter i_dsi3_filter (
		.clk_rst               (clk_rst             ), 
		.i_rx                  (i_rx                ),
		.i_shorter_filter_time ((i_sample_cfg=='0)?1'b1:1'b0   ),
		.chip_filtered         (chip_filtered.master), 
		.o_rx_test             (o_rx_test           ));
	
	assign o_rx_filtered[0] = ((chip_filtered.chip == C1) || (chip_filtered.chip == C2)) ? 1'b1 : 1'b0;
	assign o_rx_filtered[1] = (chip_filtered.chip == C2) ? 1'b1 : 1'b0;

	/*###   sample received chip   ######################################################*/
	logic	received_3_C0_chips;
	logic	chip_ready;
	logic	next_chip_not_C0;
	logic	receiving_started_tick;
	logic	stop_receiving;

	dsi3_receive_sampling i_dsi3_receive_sampling (
			.clk_rst		  (clk_rst	             ),
			.i_enable	      (i_enable_receiver     ),
			.i_sample_cfg     (i_sample_cfg          ),
			.i_stop_receiving (stop_receiving        ),
			.chip_in		  (chip_filtered.slave   ),
			.chip_out	      (chip_sampled.master   ),
			.o_chip_ready     (chip_ready            ),
			.o_receiving	  (o_rec_pending         ),
			.o_rec_start_tick (receiving_started_tick));
	
	assign	o_receiving_started_tick = receiving_started_tick;

	/*###   symbol building and word generation   ######################################################*/
	always_comb begin
		if (chip_ready == 1'b1) begin
			if (chip_filtered.chip != C0) begin
				next_chip_not_C0 = 1'b1;
			end
			else begin
				next_chip_not_C0 = 1'b0;
			end
		end
		else  begin
			next_chip_not_C0 = 1'b0;
		end
	end

	dsi3_pkg::dsi3_symbol	symbol_out;
	logic		symbol_ready;
	dsi3_symbol_builder i_dsi3_symbol_builder (
			.clk_rst			  (clk_rst			 ),
			.chip_in			  (chip_sampled.slave),
			.i_chip_ready		  (chip_ready	     ),
			.i_enable			  (i_enable_receiver ),
			.i_stop_receiving	  (stop_receiving    ),
			.i_next_chip_not_C0	  (next_chip_not_C0  ),
			.o_received_0_as_first(received_3_C0_chips ),
			.o_symbol_ready	   	  (symbol_ready		 ),
			.o_symbol			  (symbol_out		 ),
			.o_received_c0_after_packet(o_received_c0_after_packet));

	/*###   symbol conversion & checking   ######################################################*/
	logic[3:0]	symbol_decoded;
	logic		error_invalid_chip, error_invalid_symbol;
	dsi3_symbol_lut_module i_dsi3_symbol_lut (
			.symbol_in			  (symbol_out		    ),
			.symbol_out			  (symbol_decoded	    ),
			.error_invalid_chip	  (error_invalid_chip   ),
			.error_invalid_symbol (error_invalid_symbol ));
	
	assign	o_symbol_error_set = (error_invalid_chip | error_invalid_symbol) & (symbol_ready);

	/*###   collecting data   ######################################################*/
	dsi3_receive_data_collect i_dsi3_receive_data_collect (
		.clk_rst                  (clk_rst                 ), 
		.i_enable_receiver        (i_enable_receiver       ),
		.i_symbol_ready           (symbol_ready            ), 
		.i_symbol                 (symbol_decoded          ), 
		.i_response_finished      (received_3_C0_chips     ),
		.i_receive_time_out       (i_receive_time_out      ),
		.i_rec_pending            (o_rec_pending           ),
		.i_receiving_started_tick (receiving_started_tick  ),
		.o_stop_receiving         (stop_receiving          ),
		.o_received_data          (o_received_data         ), 
		.o_response_finished      (o_response_finished     ), 
		.o_data                   (o_data                  ), 
		.o_symbol_count           (o_symbol_count          ), 
		.o_symbol_count_overflow  (o_symbol_count_overflow ));

endmodule
