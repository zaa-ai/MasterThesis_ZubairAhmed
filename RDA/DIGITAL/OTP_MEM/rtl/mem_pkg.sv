package mem_pkg;

	localparam int c_ip_wl_adr = 12;
	localparam int c_ip_wl_dat = 12;
	localparam int c_ip_wl_sel = 2;
	typedef struct packed {
		logic [11:0] adr;
		logic [11:0] dat;
		logic we;
		logic [1:0] sel;
		logic stb;
		logic ack;
		logic otp_ready;
	} t_ip_bus;
endpackage
