/*------------------------------------------------------------------------------
 * File          : tdma_writer_if.svh
 * Project       : p52144
 * Author        : jvoi
 * Creation date : Feb 17, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

interface tdma_writer_if ();
	import tdma_pkg::*;
	import project_pkg::*;
	
	tdma_writer_action_t	action;
	logic	acknowledge;
	data_ecc_t		packet_index;
	tdma_packet_ecc_t	packet;
	tdma_header_ecc_t	header;
	
	modport master (
			output	action,
			output	packet_index, packet, header,
			input	acknowledge
	);
	
	modport slave (
			input	action,
			input	packet_index, packet, header,
			output	acknowledge
	);
	
endinterface : tdma_writer_if