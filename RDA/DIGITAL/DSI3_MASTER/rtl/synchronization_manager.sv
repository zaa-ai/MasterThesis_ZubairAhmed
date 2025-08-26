`include "global_defines.sv"
/**
 * Module: synchronization_manager
 * 
 * module managing synchronization of all DSI3 channels
 */
module synchronization_manager import project_pkg::*; import dsi3_pkg::*;(
		clk_reset_if.slave	clk_rst,
		synchronization_if.slave	sync[DSI_CHANNELS-1:0],
		pad_int_if.master			syncb_pad,
		input	dsi_logic_t			i_register_sync,
        input   logic               i_sync_master,
        input   logic               i_tick_1us,
		output	dsi_logic_t			o_sync_error,
		output	logic				o_syncb
	);
	logic  syncb_oe, syncb_pd, syncb_out;
	
	channel_selector_t	channels_to_synchronize[DSI_CHANNELS-1:0];
	logic syncb;
	generate
		genvar channel;
		for (channel = 0; channel < DSI_CHANNELS; channel++) begin:generate_block_synchronization_managers
			synchronization_manager_block i_synchronization_manager_block (
				.clk_rst                    (clk_rst                    ), 
				.sync                       (sync[channel]              ), 
				.i_channels_to_synchronize  (channels_to_synchronize    ),
				.i_register_sync            (i_register_sync[channel]   ),
				.i_external_sync            (syncb                      ),
				.o_channels_to_synchronize  (channels_to_synchronize[channel] ),
				.o_sync_error               (o_sync_error[channel]      ));
		end
    endgenerate
    
    dsi_logic_t fire_per_channel, ready;
    
    logic   fire;
    
    
    // P muss registriert sein (currently_registered_channels)
    // es müssen alle beteiligten Kanäle warten (außer P)
    
    genvar i;
    generate
        for (i = 0; i < DSI_CHANNELS; i++) begin : generate_fire_conditions
            assign  fire_per_channel[i] = (&((~sync[i].currently_registered_channels[DSI_CHANNELS-1:0]) | ready)) & sync[i].currently_registered_channels[DSI_CHANNELS];
            assign  ready[i] = sync[i].waiting;
        end
    endgenerate
    
    assign  fire = |(fire_per_channel);
	
	sync i_sync_syncb (
		.clk_rst     (clk_rst        ), 
		.i_in        (syncb_pad.in_a ), 
		.o_test_out  (               ), 
		.o_out       (syncb          ));
    
    dsi3_sync_master i_dsi3_sync_master (
        .clk_rst                (clk_rst                ),
        .i_fire                 (fire                   ),
        .i_tick_1us             (i_tick_1us             ),
        .i_sync_master          (i_sync_master          ),
        .o_syncb_out            (syncb_out              )
    );
    
	`PAD_INST(syncb_pad, syncb_oe, syncb_out, syncb_pd, 1'b0, 1'b1)
    
    assign  syncb_pd = (i_sync_master == 1'b1) ? 1'b0 : 1'b1;
    assign  syncb_oe = (i_sync_master == 1'b1) ? 1'b1 : 1'b0;
	
	assign	o_syncb = syncb;
	
endmodule


