/**
 * Interface: elip_if
 * 
 * ELIP Interface
 */
interface elip_if #(
		parameter addr_width=8,
		parameter data_width=8
	);
	
	logic	wr;
	logic	rd;
	logic[addr_width-1:0]	addr;
	logic[data_width-1:0]	data_write;
	
	modport master (
			output	wr, rd, addr, data_write
		);
	
	modport slave (
			input	wr, rd, addr, data_write
		);

endinterface


