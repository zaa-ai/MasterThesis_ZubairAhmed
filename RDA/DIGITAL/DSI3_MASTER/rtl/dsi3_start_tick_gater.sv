/**
 * Module: dsi3_start_tick_gater
 * 
 * module gating tick signals used for starting DSI3 communications
 */
module dsi3_start_tick_gater import project_pkg::*;(
		clk_reset_if.slave			clk_rst,
		input	logic				i_register_sync,
		input	logic				i_fire_sync,
		input	logic				i_reset_sync,
		input	channel_selector_t	i_registered_channels,
		input	logic				i_tx_shift_is_zero,
		input	dsi_logic_t			i_start_ticks_of_channels_before,
		input	dsi_logic_t			i_gate_of_previous_channels,
		
		output	logic				o_gate
	);
	
	logic			gater, gater_next;
	dsi_logic_t		registered_channels;
	logic			fired, fired_ff, fired_ff_next;
	logic			one_of_the_ticks_in_previous_registered_channels;
	
	always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0)  begin
			gater <= 1'b0;
			fired_ff <= 1'b0;
			registered_channels <= '0;
		end
		else begin
			gater <= gater_next;
			fired_ff <= fired_ff_next;
			if (i_register_sync == 1'b1)
				registered_channels <= i_registered_channels[DSI_CHANNELS-1:0];
		end
	end
	
	assign	fired = i_fire_sync | fired_ff;
	
	always_comb begin
		o_gate = gater;
		gater_next = gater;
		fired_ff_next = fired_ff;
		if (gater == 1'b0) begin
			if (i_register_sync == 1'b1) begin
				gater_next = 1'b1;
				fired_ff_next = 1'b0;
			end
		end
		else begin
			if (i_reset_sync == 1'b1) begin
				o_gate = 1'b0;
				gater_next = 1'b0;
			end
			if (fired == 1'b1) begin
				fired_ff_next = 1'b1;
				if (i_tx_shift_is_zero == 1'b1) begin
					o_gate = 1'b0;
					gater_next = 1'b0;
				end
				else begin
					if ((i_gate_of_previous_channels & registered_channels) == '0) begin
						if (one_of_the_ticks_in_previous_registered_channels == 1'b1) begin
							o_gate = 1'b0;
							gater_next = 1'b0;
						end
					end
				end
			end
		end
	end
	
	assign	one_of_the_ticks_in_previous_registered_channels = |(i_start_ticks_of_channels_before & registered_channels);


endmodule


