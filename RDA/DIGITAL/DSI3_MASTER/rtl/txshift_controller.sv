/**
 * Module: txshift_controller
 * 
 * controller for generating TXSHIFT for all DSI3 channels
 */
module txshift_controller import project_pkg::*; (
		clk_reset_if.slave	clk_rst,
		dsi3_common_config_if.slave	common_config,
		input	logic		i_run,
		output	dsi_logic_t	o_tick
	);
	
	import dsi3_pkg::*;
	
	logic	run, run_next;
	logic	initial_start_tbit;
	
	logic		start_tbit, tick_tbit;
	
	logic[8:0]	tbit_shift_time_nominal;
	logic[9:0]	tbit_shift_time;
	
	logic[DSI_CHANNELS-2:0]	start_shift, tick_transmit_shifted;
	
	assign	tbit_shift_time_nominal = 9'((18*4)<<(get_bit_time_shift(common_config.bit_time))); // (32/2)us*18MHz = 288 ; P52143-449 
	assign	tbit_shift_time = ({2'b00, common_config.tx_shift} >= tbit_shift_time_nominal) ? ({1'b0,tbit_shift_time_nominal}<<1) : {1'b0, tbit_shift_time_nominal};
	
	tbit_generator #(10) i_tbit_generator (
			.clk_rst     (clk_rst    ), 
			.i_tick      (start_tbit ), 
			.i_shift     (tbit_shift_time),
			.o_tick      (tick_tbit  ));

	shift_generator #(7) i_transmit_tx_shift_generator [DSI_CHANNELS-2:0](
			.clk_rst     (clk_rst                ), 
			.i_tick      (start_shift), 
			.i_shift     (common_config.tx_shift ),
			.o_tick      (tick_transmit_shifted ));
	
	always_ff@(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0) begin
			run <= 1'b0;
		end
		else begin
			run <= run_next;
		end
	end
	
	assign	run_next = i_run;
	assign	initial_start_tbit = ~run & i_run;
	
	always_comb begin
		start_tbit = (tick_tbit & i_run)  | initial_start_tbit;
	end
	
	always_comb begin
		o_tick[0] = start_tbit;
		for (int i=1; i<DSI_CHANNELS; i++) begin
			if (common_config.tx_shift == '0) begin
				o_tick[i] = start_tbit;
			end
			else begin
				o_tick[i] = tick_transmit_shifted[i-1];
			end
		end
	end
	
	assign	start_shift[0] = start_tbit;
	generate
		if (DSI_CHANNELS>2) begin : generate_start_shift
			assign start_shift[DSI_CHANNELS-2:1] = tick_transmit_shifted[DSI_CHANNELS-3:0];
		end
	endgenerate
	
endmodule
