/**
 * Module: dsi3_start_manager
 * 
 * manages starts of transmissions (synchronizes channels and time shifts and ...)
 */
module dsi3_start_manager import project_pkg::*; import dsi3_pkg::*;(
		clk_reset_if.slave 			clk_rst,
		dsi3_common_config_if.slave common_config,
		
		dsi3_start_request_if.slave	request[DSI_CHANNELS-1:0],
		synchronization_if.slave	sync[DSI_CHANNELS-1:0],
		
		pad_int_if.master			syncb_pad,
		input	dsi_logic_t			i_register_sync,
        input   logic               i_sync_master,
        input   logic               i_tick_1us,
		output	dsi_logic_t			o_sync_error,
		output	logic				o_syncb
	);
	
	dsi_logic_t		gate_tick;
	
	dsi3_start_request_if request_after_sync[DSI_CHANNELS-1:0] ();
	
	generate
		genvar channel;
		genvar k;

		for (channel = 0; channel < DSI_CHANNELS; channel++) begin : channel_specific_assignments
			assign	request[channel].pdcm_period_running	= request_after_sync[channel].pdcm_period_running;
			assign	request[channel].tick_pdcm	 			= request_after_sync[channel].tick_pdcm & ~gate_tick[channel];
			assign	request[channel].tick_transmit 			= request_after_sync[channel].tick_transmit & ~gate_tick[channel];
			assign	request[channel].pdcm_receive_timeout	= request_after_sync[channel].pdcm_receive_timeout;
			
			assign	request_after_sync[channel].pdcm_period			= request[channel].pdcm_period;
			assign	request_after_sync[channel].mode 				= request[channel].mode;
			assign	request_after_sync[channel].transmitting 		= request[channel].transmitting;
			assign	request_after_sync[channel].pdcm_in_progress 	= request[channel].pdcm_in_progress;

			assign	request_after_sync[channel].request			 	= request[channel].request & ~(sync[channel].armed);
			
			dsi_logic_t	start_ticks_of_channels_before;
			dsi_logic_t	gate_tick_of_previous_channels;
			
			for (k=0; k < DSI_CHANNELS; k++) begin : generate_start_tick_channels
				if (k <= channel)	
					assign start_ticks_of_channels_before[k] = request_after_sync[k].tick_transmit;
				else
					assign start_ticks_of_channels_before[k] = 1'b0;
				if (k < channel)	
					assign gate_tick_of_previous_channels[k] = gate_tick[k];
				else
					assign gate_tick_of_previous_channels[k] = 1'b0;
			end
			
			dsi3_start_tick_gater i_dsi3_start_tick_gater (
				.clk_rst                           (clk_rst                          ), 
				.i_register_sync                   (sync[channel].register           ), 
				.i_fire_sync                       (sync[channel].fire               ), 
				.i_reset_sync                      (sync[channel].reset              ),
				.i_registered_channels             (sync[channel].channels_to_sync   ), 
				.i_tx_shift_is_zero                ((common_config.tx_shift == '0) ? 1'b1 : 1'b0), 
				.i_start_ticks_of_channels_before  (start_ticks_of_channels_before   ), 
				.i_gate_of_previous_channels       (gate_tick_of_previous_channels   ),
				.o_gate                            (gate_tick[channel]               ));
			
		end
		
	endgenerate
	
	dsi3_start_tick_generator i_dsi3_start_tick_generator (
		.clk_rst        (clk_rst            ), 
		.common_config  (common_config      ), 
		.request        (request_after_sync.slave ),
		.gate_pdcm		(gate_tick)
	);
	
	synchronization_manager i_synchronization_manager (
		.clk_rst          (clk_rst         ), 
		.sync             (sync            ), 
		.syncb_pad        (syncb_pad       ), 
		.i_register_sync  (i_register_sync ),
        .i_sync_master    (i_sync_master   ),
        .i_tick_1us       (i_tick_1us      ),
		.o_sync_error     (o_sync_error    ), 
		.o_syncb          (o_syncb         ));
	
endmodule


