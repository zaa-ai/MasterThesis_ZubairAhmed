/**
 * Interface: buffer_writer_if
 *
 * Interface for writing into buffer
 * 
 */
interface pdcm_buffer_writer_if(	);
	import project_pkg::*;
	import buffer_if_pkg::*;

	logic full, ready, nearly_full;
	data_ecc_t	data;
	pdcm_buffer_writer_action_e	action;


	modport master (
			output	data,
			output	action,
			input	full, nearly_full, ready
		);

	modport slave (
			input	data,
			input	action,
			output	full, nearly_full, ready
		);
endinterface
