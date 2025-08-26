/**
 * Interface: otp_ip_bus
 * 
 * interface connecting to OTP wrapper
 */
interface otp_ip_bus_if #(
		parameter addr_width=8,
		parameter data_width=12
	);

	logic[addr_width-1:0]	addr;
	logic[data_width-1:0]	data;
	logic					we;
	logic[1:0]				sel;
	logic					stb;
	logic					ack;
	logic					sleep;
	logic[1:0]				read_mode;
	
	modport master(
		input  ack, data,
		output  addr, we, sel, stb, sleep, read_mode
	);
	
	modport slave(
		input  addr, we, sel, stb, sleep, read_mode,
		output  ack, data
	);	

endinterface


