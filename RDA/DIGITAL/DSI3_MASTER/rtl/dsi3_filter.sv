/**
 * Module: dsi3_filter
 * 
 * Filter for DSI3 inputs
 */
module dsi3_filter  import dsi3_pkg::*; (
		clk_reset_if.slave	clk_rst,
		input	logic[1:0]	i_rx,			// DSI3 current comparator input (MSB=higher current, LSB=lower current)
		input	logic		i_shorter_filter_time,
		dsi3_chip_if.master chip_filtered,
		output	logic[1:0]	o_rx_test
	);
	
	logic[1:0]	rx_sync;
	dsi3_chip_if chip_in();
	dsi3_chip	chip, chip_next;
	
	// sync
	sync #(.SIZE(2)) i_sync_dsi3_rxd (
			.clk_rst     (clk_rst    ),
			.i_in        (i_rx       ),
			.o_test_out  (o_rx_test  ),
			.o_out       (rx_sync    ));
	
	/*###   convert receiver output to chip   ######################################################*/
	dsi3_chip_converter i_dsi3_chip_converter (
			.receiver_output (rx_sync        ),
			.dsi3_chip_out	 (chip_in.master ));
	
	/*###   input chip filter   ######################################################*/
	dsi3_filter_counter_t   filter_counter_chip0,filter_counter_chip1,filter_counter_chip2, max_value;
	dsi3_chip_filter_counter#(.COUNT_VALUE(dsi3_pkg::C0)) i_filter_counter0(.clk_rst(clk_rst),.i_input_value(chip_in.chip),.i_filtered_value(chip_next), .i_shorter_filter_time(i_shorter_filter_time), .o_cnt(filter_counter_chip0));
	dsi3_chip_filter_counter#(.COUNT_VALUE(dsi3_pkg::C1)) i_filter_counter1(.clk_rst(clk_rst),.i_input_value(chip_in.chip),.i_filtered_value(chip_next), .i_shorter_filter_time(i_shorter_filter_time), .o_cnt(filter_counter_chip1));
	dsi3_chip_filter_counter#(.COUNT_VALUE(dsi3_pkg::C2)) i_filter_counter2(.clk_rst(clk_rst),.i_input_value(chip_in.chip),.i_filtered_value(chip_next), .i_shorter_filter_time(i_shorter_filter_time), .o_cnt(filter_counter_chip2));
	
	always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0)  begin
			chip <= C0;
		end else begin
			chip <= chip_next;
		end
	end
	
	always_comb begin
		if (i_shorter_filter_time == 1'b1)
			max_value = 4'd10;
		else
			max_value = '1;
	end
	
	always_comb begin
		chip_next = chip;
		if (filter_counter_chip0 == max_value)
			chip_next = C0;
		else if (filter_counter_chip1 == max_value)
			chip_next = C1;
		else if (filter_counter_chip2 == max_value)
			chip_next = C2;
	end
	
	assign	chip_filtered.chip = chip;
	
endmodule


