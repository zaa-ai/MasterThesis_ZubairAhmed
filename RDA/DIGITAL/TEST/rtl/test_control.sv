/**
 * Module: test_control
 * 
 * Module including all test stuff and OTP inclusive wrapper
 */
module test_control import jtag_tap_pkg::*; import project_pkg::*; (
		clk_reset_if.master	clk_rst,
		clk_reset_if.master	clkosc_rst,
		clk_reset_if		clk_rst_jtag,
		
		jtag_pad_if.slave 	jtag_pad,
		jtag_bus_if.master	jtag_bus,
		tmr_scan_if.master	tmr_scan,
		clock_switch_if.slave  	clock_switch_io,
		
		elip_full_if.master	elip,
		
		input	jtag_dr_for_registers_t	i_jtag_dr,
		input	logic			i_resb,
		input	logic			i_porb,
		
		otp_io_if.master		otp_io,
		otp_ip_bus_if.slave		otp_ip_bus
	);
	
	import	mem_pkg::*;
	import	otp_wrapper_pkg::*;
	
	// @SuppressProblem -type partially_unread_data -count 1 -length 1
	t_ip_bus	i_ip_bus, o_ip_bus;
	jtag_status_if status ();
	jtag_dr_for_registers_t		jtag_dr_test_registers;
	jtag_dr_t	jtag_dr, dr_elip, jtag_dr_standard;
	
	// @SuppressProblem -type partially_unread_data -count 1 -length 1
	t_jtag_bus	i_jtag, o_jtag;
	
	assign	jtag_dr = {16'h0000,(i_jtag_dr | jtag_dr_test_registers)} | dr_elip | jtag_dr_standard | o_jtag.dsr;
	
	`include "OTP_test_registers_if_inst.sv"
	`include "scan_registers_if_inst.sv"
	`include "JTAG_standard_registers_if_inst.sv"
	
	jtag_tap i_jtag_tap (
		.status        (status.master       ), 
		.pads          (jtag_pad     ), 
		.i_atpgmode    (scan_registers_SCAN.SCAN         ), 
		.i_dr          (jtag_dr      ),
		.i_dsr2tdo     (o_jtag.dsr2tdo),
		.i_tdo_latched (o_jtag.tdo_latched),
		.i_tdo_unlatched(o_jtag.tdo_unlatched));
	
	assign	jtag_bus.addr = status.ir;
	assign	jtag_bus.data_write = status.dsr[31:16]; // TODO: get numbers from EDF..
	assign	jtag_bus.wr = status.update_dr_fe;
	assign	jtag_bus.rd = status.capture_dr_fe;
	
	assign	jtag_bus.clk =  jtag_pad.tck;
	assign	jtag_bus.rstn = jtag_pad.trstn;
	
	clk_reset_if int_clk_rst ();
	clk_reset_if int_clk_rst_jtag ();
	assign	int_clk_rst_jtag.clk = jtag_pad.tck;
	assign	int_clk_rst_jtag.rstn = jtag_pad.trstn;
	assign	clk_rst.clk = int_clk_rst.clk;
	assign	clk_rst.rstn = int_clk_rst.rstn;
	assign	clk_rst_jtag.clk = int_clk_rst_jtag.clk;
	assign	clk_rst_jtag.rstn = int_clk_rst_jtag.rstn;
	assign	clkosc_rst.rstn = int_clk_rst.rstn;
	assign	clkosc_rst.clk = clock_switch_io.clock_osc;
	
	clk_reset_if scan_registers_clk_rst ();
	assign	scan_registers_clk_rst.clk = jtag_pad.tck;
	assign	scan_registers_clk_rst.rstn = jtag_pad.tmode;
	
	
	OTP_test_registers #(
		.base_addr                   (BASE_ADDR_TEST_OTP         ), 
		.addr_width                  (JTAG_IR_WIDTH              )
	) i_OTP_test_registers (
		.clk_rst                     (int_clk_rst_jtag.slave           ), 
		.addr                        (jtag_bus.addr              ), 
		.data_in                     (jtag_bus.data_write        ), 
		.wr                          (jtag_bus.wr                ), 
		.rd                          (jtag_bus.rd                ), 
		.data_out                    (jtag_dr_test_registers     ), 
		.OTP_test_registers_OTP_WRITE_PULSE_WIDTH(OTP_test_registers_OTP_WRITE_PULSE_WIDTH.master));
	
	scan_registers #(
		.base_addr            (BASE_ADDR_TEST_SCAN        ), 
		.addr_width           (JTAG_IR_WIDTH              )
		) i_scan_registers (
		.clk_rst              (scan_registers_clk_rst.slave     ), 
		.addr                 (jtag_bus.addr              ), 
		.data_in              (jtag_bus.data_write        ), 
		.wr                   (jtag_bus.wr                ), 
		.rd                   (jtag_bus.rd                ),
		.data_out             (                           ), // needs to be empty, otherwise scan pattern is dependent on register settings (P52143-420)
		.scan_registers_SCAN  (scan_registers_SCAN.master ));
	
	JTAG_standard_registers #(
		.base_addr                            (BASE_ADDR_TEST_TOP                         ), 
		.addr_width                           (JTAG_IR_WIDTH                              )
		) i_JTAG_standard_registers (
		.clk_rst                              (int_clk_rst_jtag.slave                     ), 
		.addr                                 (jtag_bus.addr                              ), 
		.data_in                              ('0                                         ), 
		.wr                                   (1'b0                                       ), 
		.rd                                   (jtag_bus.rd                                ), 
		.data_out                             (jtag_dr_standard                           ), 
		.JTAG_standard_registers_JTAG_ID      (JTAG_standard_registers_JTAG_ID.master     ), 
		.JTAG_standard_registers_JTAG_BYPASS  (JTAG_standard_registers_JTAG_BYPASS.master ));
	
	// save settings when scan is enabled
	assign	scan_registers_SCAN.SCAN_set			= scan_registers_SCAN.SCAN;
	assign	scan_registers_SCAN.COMPRESSION_set		= scan_registers_SCAN.SCAN;
	assign	scan_registers_SCAN.VDD_ILOAD_DIS_set	= scan_registers_SCAN.SCAN;
	assign	scan_registers_SCAN.VDD_RDIV_DIS_set	= scan_registers_SCAN.SCAN;
	assign	scan_registers_SCAN.VDD_DIS_set			= scan_registers_SCAN.SCAN;
	assign	scan_registers_SCAN.DISABLE_OSC_set		= scan_registers_SCAN.SCAN;
	
	assign	scan_registers_SCAN.SCAN_in 			= scan_registers_SCAN.SCAN;
	assign	scan_registers_SCAN.COMPRESSION_in 		= scan_registers_SCAN.COMPRESSION;
	assign	scan_registers_SCAN.VDD_ILOAD_DIS_in 	= scan_registers_SCAN.VDD_ILOAD_DIS;
	assign	scan_registers_SCAN.VDD_RDIV_DIS_in 	= scan_registers_SCAN.VDD_RDIV_DIS;
	assign	scan_registers_SCAN.VDD_DIS_in			= scan_registers_SCAN.VDD_DIS;
	assign	scan_registers_SCAN.DISABLE_OSC_in		= scan_registers_SCAN.DISABLE_OSC;
	
	assign	tmr_scan.scan = scan_registers_SCAN.SCAN;
	assign	tmr_scan.vdd_voltage_divider_disable = scan_registers_SCAN.VDD_RDIV_DIS;
	assign	tmr_scan.vdd_disable = scan_registers_SCAN.VDD_DIS;
	assign	tmr_scan.vdd_load_disable = scan_registers_SCAN.VDD_ILOAD_DIS;
	assign	tmr_scan.disable_osc = scan_registers_SCAN.DISABLE_OSC;
	
	
	//*###   JTAG ELIP ACCESS   ######################################################*/
	jtag_elip i_jtag_elip (
		.clk_rst       (int_clk_rst.slave  ), 
		.jtag_clk_rst  (int_clk_rst_jtag.slave ), 
		.status        (status.slave       ), 
		.elip          (elip         ),
		.o_data_shift_register(dr_elip));
	
	//*###   reset   ######################################################*/
	clk_reset_if clk_rst_resb_deb ();
	logic	rstn_resb_deb, rstn_resb_deb_scan_muxed;
	logic	rstn_por, rstn_por_resb;
	logic	resb_sync, resb_deb;
	logic	porb_muxed;

	assign	clk_rst_resb_deb.clk = ~clkosc_rst.clk;
	assign	clk_rst_resb_deb.rstn = rstn_resb_deb_scan_muxed;

	sync_reset i_sync_reset (
		.clk                   (clock_switch_io.clock_osc), 
		.rstn_async            (porb_muxed               ), 
		.o_rstn                (rstn_por                 ), 
		.o_rstn_clock_posedge  (rstn_resb_deb            ));
	
	pure_mux i_scan_mux_reset_resb_deb (
			.i_a         (tmr_scan.scan_reset), 
			.i_b         (rstn_resb_deb), 
			.i_sa        (scan_registers_SCAN.SCAN), 
			.o_y         (rstn_resb_deb_scan_muxed       ));
	
	pure_and i_pure_and_reset_por_resb (
		.i_a         (rstn_por        ), 
		.i_b         (resb_deb        ), 
		.o_y         (rstn_por_resb   ));
	
	pure_mux i_scan_mux_porb (
		.i_a (tmr_scan.scan_reset ),
		.i_b (i_porb ),
		.i_sa(scan_registers_SCAN.SCAN),
		.o_y (porb_muxed )
	);
	
	pure_mux i_scan_mux_reset (
			.i_a         (tmr_scan.scan_reset), 
			.i_b         (rstn_por_resb), 
			.i_sa        (scan_registers_SCAN.SCAN), 
			.o_y         (int_clk_rst.rstn       ));
	
	//*###   RESB debounce   ######################################################*/
	sync i_sync_resb (
		.clk_rst     (clk_rst_resb_deb.slave    ), 
		.i_in        (i_resb     ), 
		.o_test_out  ( ), 
		.o_out       (resb_sync  ));
	
	deb #(
		.DEBOUNCE_TIME  (RESB_DEB_TIME ), 
		.RESET_VALUE    (1'b0   )
	) i_deb_resb (
		.clk_rst        (clk_rst_resb_deb.slave    ), 
		.i_in           (resb_sync  ), 
		.o_out          (resb_deb   ));
	
	//*###   Clock Switch OSC/PLL   ######################################################*/
	logic	switched_clock, clock_switched;
	clock_switch i_clock_switch (
			.i_clk1     	(clock_switch_io.clock_osc ), 
			.i_clk2     	(clock_switch_io.clock_pll ), 
			.i_sel_clk2  	(clock_switch_io.select_clock_pll),
			.i_rstn     	(int_clk_rst.rstn), 
			.i_tst_en		(clock_switch_io.test_en),
			.i_tst_sel		(clock_switch_io.test_sel),
			.o_clk			(switched_clock             ),
			.o_clk_switched	(clock_switched));
	assign	clock_switch_io.clock_switched = (scan_registers_SCAN.SCAN == 1'b0) ? clock_switched : clock_switch_io.select_clock_pll; // for scan coverage
	
	pure_mux i_pure_mux_system_clock (
			.i_a         (tmr_scan.scan_clock ), 
			.i_b         (switched_clock      ), 
			.i_sa        (scan_registers_SCAN.SCAN       ), 
			.o_y         (int_clk_rst.clk        ));
	
	/*###   OTP   ######################################################*/

	//*###   OTP IP bus connection   ######################################################*/
	assign	i_ip_bus.ack = '0;
	assign	i_ip_bus.adr = otp_ip_bus.addr;
	assign	i_ip_bus.dat = '0;
	assign	i_ip_bus.sel = otp_ip_bus.sel;
	assign	i_ip_bus.stb = otp_ip_bus.stb;
	assign	i_ip_bus.we = otp_ip_bus.we;
	assign	i_ip_bus.otp_ready = 1'b0;
	assign	otp_io.otp_ready = o_ip_bus.otp_ready;

	assign	otp_ip_bus.data	= o_ip_bus.dat;
	assign	otp_ip_bus.ack	= o_ip_bus.ack;
	
	/*###   JTAG tap bus connection   ######################################################*/
	assign	i_jtag.capture_dr = status.capture_dr;
	assign	i_jtag.capture_dr_fe = status.capture_dr_fe;
	assign	i_jtag.dsr = status.dsr;
	assign	i_jtag.dsr2tdo = 1'b1;
	assign	i_jtag.ir = status.ir;
	assign	i_jtag.run_idle = status.run_idle;
	assign	i_jtag.run_idle_fe = status.run_idle_fe;
	assign	i_jtag.shift_dr= status.shift_dr;
	assign	i_jtag.shift_dr_fe = status.shift_dr_fe;
	assign	i_jtag.tck = jtag_pad.tck;
	assign	i_jtag.tdi = jtag_pad.tdi;
	assign	i_jtag.tms = jtag_pad.tms;

	assign	i_jtag.test_en = (tmr_scan.scan == 1'b0) ? jtag_pad.tmode : tmr_scan.scan_reset;

	assign	i_jtag.tdo_latched = 1'b0;
	assign	i_jtag.tdo_unlatched = 1'b0;
	assign	i_jtag.test_rst = status.test_rst;
	assign	i_jtag.test_rst_fe = status.test_rst_fe;
	assign	i_jtag.update_dr = status.update_dr;
	assign	i_jtag.update_dr_fe = status.update_dr_fe;
	assign	i_jtag.update_ir = status.update_ir;
	assign	i_jtag.update_ir_fe = status.update_ir_fe;
	
	mem i_otp_wrapper(
			.i_sys_clk          (int_clk_rst.clk),
			.i_rst_n            (int_clk_rst.rstn),
			.i_por_n            (int_clk_rst.rstn),
			.i_atpg_mode        (scan_registers_SCAN.SCAN),
			.i_ip_bus           (i_ip_bus),
			.o_ip_bus           (o_ip_bus),
			.i_sleep_mode       (otp_ip_bus.sleep),
			.i_jtag_bus         (i_jtag),
			.o_jtag_bus         (o_jtag),
			.a_otp_ehv          (otp_io.a_ehv),
			.a_otp_vbg          (otp_io.a_vbg),
			.a_otp_vpppad       (otp_io.a_vpp),
			.a_otp_vref         (otp_io.a_vref),
			.a_otp_vrr          (otp_io.a_vrr),
			.i_read_mode		(otp_ip_bus.read_mode),
			.i_otp_write_config (OTP_test_registers_OTP_WRITE_PULSE_WIDTH.PULSE_WIDTH));
	
endmodule
