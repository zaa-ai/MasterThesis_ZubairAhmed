/**
 * Interface: dsi3_start_request_if
 * 
 * interface for starting DSI3 transmissions from DSI3 block which are managed by a synchronisation and start manager
 */
interface dsi3_start_request_if;
	import 			dsi3_pkg::*;
	import			project_pkg::*;
	
	channel_mode_t	mode;				// mode of the next transmission (PDCM / CRM)
	logic	request;					// requests a start tick
	data_t	pdcm_period;
	
	logic	pdcm_period_running;		// signals that the period of a particular PDCM period is not over
	
	logic	pdcm_in_progress;			// signals that the FSM is still in the same PDCM command
	
	logic	transmitting;				// shows the start logic, that a transmission is ongoing and new transmission have to sorted into the cycle
	logic	tick_pdcm, tick_transmit;	// ticks to start transmission
	logic	pdcm_receive_timeout; 		// some time before end of period
	
	modport slave(
			input	mode, transmitting, request, pdcm_period,
			
			output	pdcm_period_running, tick_pdcm, tick_transmit,
			input	pdcm_in_progress,
			output	pdcm_receive_timeout
		);
	
	modport master(
			
			input	pdcm_period_running,
			
			output	pdcm_in_progress, pdcm_period,
			
			
			output	mode, transmitting, request,
			input	pdcm_receive_timeout, tick_pdcm, tick_transmit
			
		);
	
endinterface
