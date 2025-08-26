/**
 * Interface: jtag_bus_if
 * 
 * JTAG bus Interface
 */
interface jtag_bus_if #(
		parameter addr_width=8,
		parameter data_width=16
	);
	
	logic	clk;
	logic	rstn;
	logic	wr;
	logic	rd;
	logic[addr_width-1:0]	addr;
	logic[data_width-1:0]	data_write;
	
	modport master (
			output	wr, rd, addr, data_write,
			output	clk, rstn
		);
	
	modport slave (
			input	wr, rd, addr, data_write,
			input	clk, rstn
		);

endinterface


