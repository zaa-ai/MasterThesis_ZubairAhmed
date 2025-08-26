/**
 * Module: test_top
 * 
 * TODO: Add module documentation
 */
module test_top (
		clk_reset_if	clk_rst,
		otp_io_if		otp_io,
		otp_ip_bus_if	otp_ip_bus
	);
	
	import	mem_pkg::*;
	import	otp_wrapper_pkg::*;
	import	jtag_tap_pkg::*;
	
	/*###   OTP IP bus connection   ######################################################*/
	t_ip_bus	i_ip_bus, o_ip_bus;
	
	assign	i_ip_bus.ack = '0;
	assign	i_ip_bus.adr = otp_ip_bus.addr;
	assign	i_ip_bus.dat = '0;
	assign	i_ip_bus.sel = otp_ip_bus.sel;
	assign	i_ip_bus.stb = otp_ip_bus.stb;
	assign	i_ip_bus.we = otp_ip_bus.we;
	
	assign	otp_ip_bus.data	= o_ip_bus.dat;
	assign	otp_ip_bus.ack	= o_ip_bus.ack;
	/*###   JTAG tap bus connection   ######################################################*/
	t_jtag_bus	i_jtag, o_jtag;
	
	assign	i_jtag.capture_dr = 1'b0;
	assign	i_jtag.capture_dr_fe = 1'b0;
	assign	i_jtag.dsr = '0;
	assign	i_jtag.dsr2tdo = 1'b0;
	assign	i_jtag.ir = '0;
	assign	i_jtag.run_idle = 1'b0;
	assign	i_jtag.run_idle_fe = 1'b0;
	assign	i_jtag.shift_dr= 1'b0;
	assign	i_jtag.shift_dr_fe = 1'b0;
	assign	i_jtag.tck = 1'b0;
	assign	i_jtag.tdi = 1'b0;
	assign	i_jtag.tms = 1'b0;
	
	assign	i_jtag.test_en = 1'b0;
	
	assign	i_jtag.tdo_latched = 1'b0;
	assign	i_jtag.tdo_unlatched = 1'b0;
	assign	i_jtag.test_rst = 1'b1;
	assign	i_jtag.test_rst_fe = 1'b1;
	assign	i_jtag.update_dr = 1'b0;
	assign	i_jtag.update_dr_fe = 1'b0;
	assign	i_jtag.update_ir = 1'b0;
	assign	i_jtag.update_ir_fe = 1'b0;
	
	mem i_otp_wrapper(
			.i_sys_clk          (clk_rst.clk),
			.i_rst_n            (clk_rst.rstn),
			.i_por_n            (clk_rst.rstn),
			.i_atpg_mode        (1'b0), 
			.i_ip_bus           (i_ip_bus),
			.o_ip_bus           (o_ip_bus),
			.i_sleep_mode       (otp_ip_bus.sleep),
			.i_jtag_bus         (i_jtag),
			.o_jtag_bus         (),
			.a_otp_ehv          (otp_io.a_ehv),
			.a_otp_vbg          (otp_io.a_vbg),
			.a_otp_vpppad       (otp_io.a_vpp),
			.a_otp_vref         (otp_io.a_vref),
			.a_otp_vrr          (otp_io.a_vrr),
			.i_read_mode		(otp_ip_bus.read_mode),
			.i_otp_write_config (12'h000 )
		);
	

endmodule


