/*------------------------------------------------------------------------------
 * File          : packet_reader_if.sv
 * Project       : p52144
 * Author        : jvoi
 * Creation date : Mar 6, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

interface packet_reader_if ();
	import			project_pkg::*;
	logic			get_data; // fetch data
	logic			got_data; // data ready and assigned to data
	logic			abort;   // abort reading 
	logic			finished; // finished reading 
	data_ecc_t		data;     // data read
	
	modport master (
		output	get_data, abort,
		input	data, finished, got_data
	);
	
	modport slave (
		input	get_data, abort,
		output	data, finished, got_data
	);
	
endinterface