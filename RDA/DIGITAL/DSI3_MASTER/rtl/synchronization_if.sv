/**
 * Interface: synchronization_if
 * 
 * interface for synchronisation of different DSI3 channels
 */
interface synchronization_if;
	import	project_pkg::*;
	logic	register;
	logic	armed;
	logic	fire;
	logic	reset;
	logic	waiting;
	
	logic[DSI_CHANNELS:0]	channels_to_sync;
	logic[DSI_CHANNELS:0]	currently_registered_channels;
	
	modport master(
			input	armed, fire,
			input	currently_registered_channels,
			output	register, reset, channels_to_sync, waiting
		);
	
	modport slave(
			output	armed, fire,
			output	currently_registered_channels,
			input	register, reset, channels_to_sync, waiting
		);
	
endinterface


