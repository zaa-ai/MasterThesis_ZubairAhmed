/*------------------------------------------------------------------------------
 * File          : tdma_writer_if.svh
 * Project       : p52144
 * Author        : jvoi
 * Creation date : Feb 17, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

interface tdma_reader_if ();
	import tdma_pkg::*;
	import project_pkg::*;
	
    tdma_reader_action_t	action;
	logic	acknowledge;
    tdma_packet_index_t		packet_index;
	tdma_packet_t	packet;
	tdma_packet_t	packet_next;
	tdma_header_t	header;
	
	modport master (
			output	action,
			input	packet_index, packet, packet_next, header,
			input	acknowledge
	);
	
	modport slave (
			input	action,
			output	packet_index, packet, packet_next, header,
			output	acknowledge
	);
	
endinterface