package jtag_tap_pkg;

	localparam int c_dsr_width = 16;
	typedef struct packed {
		logic test_en;
		logic tck;
		logic tdi;
		logic tms;
		logic tdo_latched;
		logic tdo_unlatched;
		logic [7:0] ir;
		logic dsr2tdo;
		logic [31:0] dsr;
		logic test_rst;
		logic run_idle;
		logic capture_dr;
		logic shift_dr;
		logic update_dr;
		logic update_ir;
		logic test_rst_fe;
		logic run_idle_fe;
		logic capture_dr_fe;
		logic shift_dr_fe;
		logic update_dr_fe;
		logic update_ir_fe;
	} t_jtag_bus;
endpackage
