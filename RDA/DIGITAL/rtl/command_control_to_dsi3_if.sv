/**
 * Interface: command_control_to_dsi3_if
 * 
 * interface from command control to DSI3 blocks
 */
interface command_control_to_dsi3_if;
	import project_pkg::*;
	
	dsi_logic_t		clear_crm_data_buffer;
	dsi_logic_t		clear_pdcm_data_buffer;
	dsi_logic_t		stop_transmission;
	dsi_logic_t		register_sync;
	
	dsi_logic_t		dsi3_enabled;
	dsi_logic_t		clear_command_queue;
    dsi_logic_t     set_command_error;
    dsi_logic_t     set_sync_error;
	
	modport	master(
			output	clear_pdcm_data_buffer, clear_crm_data_buffer, stop_transmission, register_sync,
            output  set_command_error, set_sync_error,
			input	dsi3_enabled
		);
	
	modport	slave(
			input	clear_pdcm_data_buffer, clear_crm_data_buffer, stop_transmission, register_sync,
            input   set_command_error, set_sync_error,
			output	dsi3_enabled, clear_command_queue
		);
	
endinterface
