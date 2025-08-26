/**
 * Module: test
 *
 * top module for all test relevant features e.g. JTAG
 */
module test import project_pkg::*; (
		clk_reset_if.master	  	clk_rst,
		clk_reset_if.master	  	clkosc_rst,
		otp_io_if.master	  	otp_io,
		otp_ip_bus_if.slave	  	otp_ip_bus,
		jtag_pad_if.slave 	  	jtag,
		tmr_scan_if.master	  	tmr_scan,
		clock_switch_if.slave  	clock_switch_io,
		tmr_top_if.master		tmr_top,
		elip_full_if.master		elip,
		
		jtag_bus_if.master    	jtag_bus,
		input	jtag_dr_for_registers_t	i_jtag_dr,
		input	logic			i_resb,
		input	logic			i_porb
	);

	clk_reset_if clk_rst_jtag();
    jtag_bus_if #(.addr_width  (JTAG_IR_WIDTH ), .data_width  (JTAG_DR_WIDTH )) jtag_bus_2_test_top ();  
    jtag_dr_for_registers_t		test_top_jtag_dr, jtag_dr;
	assign	jtag_dr = i_jtag_dr | test_top_jtag_dr;
    
    assign jtag_bus_2_test_top.addr = jtag_bus.addr;
    assign jtag_bus_2_test_top.clk = jtag_bus.clk;
    assign jtag_bus_2_test_top.data_write = jtag_bus.data_write;
    assign jtag_bus_2_test_top.rd = jtag_bus.rd;
    assign jtag_bus_2_test_top.rstn = jtag_bus.rstn;
    assign jtag_bus_2_test_top.wr = jtag_bus.wr;
	
	test_control i_test_control (
		.clk_rst       (clk_rst      ),
		.clkosc_rst    (clkosc_rst   ),
		.jtag_pad      (jtag         ), 
		.jtag_bus      (jtag_bus     ), 
		.clk_rst_jtag  (clk_rst_jtag.master ),
		.clock_switch_io(clock_switch_io),
		.i_jtag_dr     (jtag_dr      ), // -> P52143-442
		.elip          (elip         ),
		.tmr_scan      (tmr_scan     ),
		.i_porb        (i_porb       ),
		.i_resb        (i_resb       ),
		.otp_io        (otp_io       ),
		.otp_ip_bus    (otp_ip_bus   ));
	
	test_top #(
		.BASE_ADDR             (BASE_ADDR_TEST_TOP   ), 
		.ADDR_WIDTH            (JTAG_IR_WIDTH        )
		) i_test_top (
		.jtag_bus              (jtag_bus_2_test_top.slave  ), 
		.tmr_top               (tmr_top              ), 
		.o_jtag_dr             (test_top_jtag_dr     ));
	
endmodule
