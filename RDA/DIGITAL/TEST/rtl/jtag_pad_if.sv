/**
 * Interface: jtag_pad_if
 * 
 * interface of JTAG pins
 */
interface jtag_pad_if;

	logic trstn;
	logic tck;
	logic tdi;
	logic tms;
	logic tdo;
	
	logic tmode;
	
	modport master(
			input	tdo,
			output	trstn, tck, tdi, tms, tmode
		);
	
	modport slave(
			output	tdo,
			input	trstn, tck, tdi, tms, tmode
		);
	
endinterface


