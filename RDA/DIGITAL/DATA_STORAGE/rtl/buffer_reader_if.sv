/**
 * Interface: buffer_reader_if
 *
 * Interface for reading data from buffer
 */
interface buffer_reader_if ();
	import project_pkg::*;
	import buffer_if_pkg::*;

	logic	empty, ready;
	data_ecc_t	data;
	buffer_reader_action_e	action;
	data_t	step; 

	modport master (
			output	action, step,
			input	data, empty, ready
		);

	modport slave (
			input	action, step,
			output	data, empty, ready
		);

endinterface
