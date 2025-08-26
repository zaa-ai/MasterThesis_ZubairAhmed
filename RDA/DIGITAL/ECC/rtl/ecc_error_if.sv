/**
 * Interface: ecc_error_if
 * 
 * interface for ECC error information
 */
interface ecc_error_if #(parameter WIDTH = 1);
	logic[WIDTH-1:0]	single_error;
	logic[WIDTH-1:0]	double_error;
	
	modport master (
		output	single_error, double_error
	);
	
	modport slave (
		input	single_error, double_error
	);

endinterface
