`ifndef _COMMON_PKG
`define _COMMON_PKG

package common_pkg;
	
	typedef int array_of_ints[];
	
	localparam CHANNELS_MSB = 11;
	localparam CHANNELS_LSB = 10;
	
	export test_addresses_pkg::*;
	export addresses_pkg::*;
	
	`include "convert_queue.svh"

	`define STRING_OF(x) `"x`"
	
	`define dut_wrapper_path	top_tb.th.i_dut_wrapper
	`define xdig_path 			`dut_wrapper_path.xtop.xdigtop
	`define xana_path 			`dut_wrapper_path.xtop.XANA
	`define LOGIC_TOP_PATH		`xdig_path.i_logic_top
	`define TRIM_OSC_PATH		`xdig_path.O_TRIM_OSC_F
	`define DSI_RX_FILTER_FAST  `xdig_path.O_DSI_RX_FILTER_FAST
	localparam string PATH_DSI3_UVB =	{`STRING_OF(`xdig_path),".I_DSI_UVB"};
	localparam string PATH_DSI3_OV =	{`STRING_OF(`xdig_path),".I_DSI_OV"};
	`define DSI_UV_DEB_PATH	 `LOGIC_TOP_PATH.i_dsi3.generate_dsi3_blocks[%1d].i_dsi3_block.uv_deb
	`define DSI_OV_DEB_PATH	 `LOGIC_TOP_PATH.i_dsi3.generate_dsi3_blocks[%1d].i_dsi3_block.ov_deb
	
	parameter string PATH_VCC_OK = {`STRING_OF(`xdig_path),".I_VCC_OK"};
	parameter string PATH_LDO_OK = {`STRING_OF(`xdig_path),".I_LDO_OK"};
	parameter string PATH_VRR_OK = {`STRING_OF(`xdig_path),".I_VRR_OK"};
	`define DSI_STATE_PATH		 `LOGIC_TOP_PATH.i_dsi3.generate_dsi3_blocks[%1d].i_dsi3_block.state
	`define DSI_ILOAD_STATE_PATH `LOGIC_TOP_PATH.i_dsi3.generate_dsi3_blocks[%1d].i_dsi3_block.i_dsi3_iload_control.state
	`define DSI_CORE_STATE_PATH	 `LOGIC_TOP_PATH.i_dsi3.generate_dsi3_blocks[%1d].i_dsi3_block.i_dsi3_core.dsi_state
	`define DSI_CHIP_IN_PATH	 `LOGIC_TOP_PATH.i_dsi3.generate_dsi3_blocks[%1d].i_dsi3_block.i_dsi3_core.i_dsi3_receive.i_dsi3_receive_sampling.chip_in.chip
	
	`define SPI_STATE_PATH		`LOGIC_TOP_PATH.i_spi.i_spi_fsm.state
	`define MAIN_STATE_PATH		`LOGIC_TOP_PATH.i_main_control.i_main_fsm.state
	`define COMMAND_CONTROL_STATE_PATH `LOGIC_TOP_PATH.i_command_control.state
    
    `define SRAM_PATH `LOGIC_TOP_PATH.i_data_storage.i_ram_wrapper_ecc_with_bist.utils_sram_with_bist_inst.utils_sram_scan_shell_inst.sync_sram_inst.sram_inst
    parameter string PATH_SRAM_MEM_ROW = {`STRING_OF(`SRAM_PATH),".mem[%0d]"};
	
	`ifdef GATE_LEVEL
		`define OTP_INST			`LOGIC_TOP_PATH.i_test.i_test_control.i_otp_wrapper.u_otpwrap_l3_top.u_otpwrap_l2_cpu.u_otpwrap_l1_jtag.u_otpwrap_l0_atpg.gen_tsmc_u_otp4kx12.u_otp4kx12
	`else
		`define OTP_INST 			`LOGIC_TOP_PATH.i_test.i_test_control.i_otp_wrapper.U_OTPWRAP_L3_TOP.U_OTPWRAP_L2_CPU.U_OTPWRAP_L1_JTAG.U_OTPWRAP_L0_ATPG.GEN_TSMC.U_OTP4KX12.u_otp4kx12
	`endif		

endpackage : common_pkg

`endif
