module otpwrap_l0_atpg();
	generate
		begin : GEN_TSMC
			otp4kx12_cp #(.dataWidth(12), .addressWidth(12), .modeWidth(8)) U_OTP4KX12 (
				.VPPEN   (),
				.VRREN   (),
				.MPP     (),
				.MRR     (),
				.CLKOUT  (),
				.PPCLKOUT(),
				.OE      (),
				.SEL     (),
				.WE      (),
				.CK      (),
				.MR      (),
				.ADDR    (),
				.DW      (),
				.DR      (),
				.EHV     (),
				.VBG     (),
				.VPPPAD  (),
				.VREF    (),
				.VRR     ()
			);
		end
	endgenerate
endmodule

module otpwrap_l1_jtag();
	otpwrap_l0_atpg U_OTPWRAP_L0_ATPG ();
endmodule

module otpwrap_l2_cpu();
	otpwrap_l1_jtag U_OTPWRAP_L1_JTAG ();
endmodule

module otpwrap_l3_top();
	otpwrap_l2_cpu U_OTPWRAP_L2_CPU ();
endmodule
/*------------------------------------------------------------------------------
 * File          : mem_black_box.sv
 * Project       : p52143
 * Author        : jvoi
 * Creation date : Sep 8, 2021
 * Description   :
 *------------------------------------------------------------------------------*/

module mem import mem_pkg::*; import otp_wrapper_pkg::*; import jtag_tap_pkg::*;(
		input	logic	i_sys_clk,
		input	logic	i_rst_n,
		input	logic	i_por_n ,
		input	logic	i_atpg_mode,
		
		input	t_ip_bus	i_ip_bus,
		output	t_ip_bus	o_ip_bus,
		input	logic	i_sleep_mode ,
		
		input	t_jtag_bus i_jtag_bus,
		output	t_jtag_bus o_jtag_bus,
		
		input	a_otp_ehv    ,
		input	a_otp_vbg    ,
		input	a_otp_vpppad ,
		input	a_otp_vref   ,
		input	a_otp_vrr,
		input	logic[1:0]	i_read_mode,
		input	logic[BL_OTP_WRITE_CONFIG-1:0]	i_otp_write_config
	);

	otpwrap_l3_top U_OTPWRAP_L3_TOP ();
	
endmodule