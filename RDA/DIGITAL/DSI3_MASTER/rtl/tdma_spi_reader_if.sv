/*------------------------------------------------------------------------------
 * File          : tdma_writer_if.svh
 * Project       : p52144
 * Author        : jvoi
 * Creation date : Feb 17, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

interface tdma_spi_reader_if ();
	import tdma_pkg::*;
	import project_pkg::*;
	
    tdma_spi_reader_action_t	action;
	logic	acknowledge;
    tdma_packet_index_t		packet_index;
    logic[7:0]      count;
	
	modport master (
			output	action, packet_index,
			input	count, 
			input	acknowledge
	);
	
	modport slave (
			input	action, packet_index,
			output	count,               
			output	acknowledge          
	);
	
endinterface