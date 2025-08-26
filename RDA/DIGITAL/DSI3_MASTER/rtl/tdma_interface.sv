/*------------------------------------------------------------------------------
 * File          : tdma_interface.sv
 * Project       : p52144
 * Author        : jvoi
 * Creation date : Jan 24, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

interface tdma_interface ();
	import tdma_pkg::*;
	
	logic			request; // high as long as request is ongoing
	logic			acknowledge;
	logic			write;
	tdma_target_t	target;
    tdma_packet_index_t		index;
	
	tdma_packet_ecc_t	packet_from_buffer, packet_to_buffer;
	tdma_header_ecc_t	header_from_buffer, header_to_buffer;
	
	
	modport master (
		input	acknowledge, packet_from_buffer, header_from_buffer,
		output	request, target, write, index, packet_to_buffer, header_to_buffer
	);
	
	modport slave (
		input	request, target, write, index, packet_to_buffer, header_to_buffer, 
		output	acknowledge, packet_from_buffer, header_from_buffer
	);
	
endinterface : tdma_interface