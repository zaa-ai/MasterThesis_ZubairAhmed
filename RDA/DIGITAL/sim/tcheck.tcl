
set searchpattern {
	"*sync*I0*" \
	"*syncff_1*" \
	"*i_spi_sync.*reg_0_" \
	"*i_utils_sync_ff_re" \
	"*u_jtag_clock_test.clk_div_reg_reg_*" \
	"*i_mux_syncro_reset_long.res_ff*" \
	"*i_mux_syncro_reset.res_ff*" "*i_syncro_test.*_reg"\
	"*sel_*_s_reg" \
	"*test_out_reg*" \
	"*u_ff_clk_resn_sig_out_reg*" \
	"*shift_dr_re_syn_reg_0*" \
        "*.i_pad_mux_test_*.test_reg_reg" \
        "*.logic_top.i_spi.txd_en_sync_reg" \
        "*.*.*.*.*.*.*.i_spi_sync.*transfer_ended_reg*0*"\
    	"*.*.*.*.*.*.*.*.*.*o_test_out_reg*0*"\
    	"*.*.*.*.*.*.*.*.*o_test_out_reg*0*"\
	"top_tb.th.i_dut_wrapper.xtop.xdigtop.i_pure_clk_gate_latch_tck.gate_inst" \
    	"top_tb.th.i_dut_wrapper.xtop.xdigtop.i_logic_top.i_dsi3.generate_dsi3_blocks_*__i_dsi3_block.i_dsi3_core.i_dsi3_receive.i_dsi3_filter.i_sync_dsi3_rxd.o_test_out_reg_*_"\
	"top_tb.th.i_dut_wrapper.xtop.xdigtop.i_logic_top.i_dsi3.generate_dsi3_blocks_*__i_dsi3_block.i_sync_deb_uv.i_deb_long.counter_reg_0_" \
    	"top_tb.th.i_dut_wrapper.xtop.xdigtop.i_logic_top.i_spi.i_spi_sync.*_reg*" \
	"top_tb.th.i_dut_wrapper.xtop.xdigtop.i_pad_mux_test_*.*test_reg_reg" \
	"top_tb.th.i_dut_wrapper.xtop.xdigtop.i_logic_top.i_test.i_test_control.jtag_elip.update_dr_synced_reg_0_" \
	"top_tb.th.i_dut_wrapper.xtop.xdigtop.i_logic_top.i_dsi3.i_dsi3_start_manager.i_synchronization_manager.i_sync_syncb.o_test_out_reg_0_" \
	"top_tb.th.i_dut_wrapper.xtop.xdigtop.i_logic_top.i_test.i_test_control.i_jtag_elip.update_dr_synced_reg_0_" \
	"top_tb.th.i_dut_wrapper.xtop.xdigtop.i_logic_top.i_timebase.i_sync_clkref.o_test_out_reg_0_" \
	"top_tb.th.i_dut_wrapper.xtop.xdigtop.i_logic_top.i_timebase.i_sync_clkref_osc.o_test_out_reg_0_" \ 
	"top_tb.th.i_dut_wrapper.xtop.xdigtop.i_pad_mux_test_intb.test_reg_reg" \
	"top_tb.th.i_dut_wrapper.xtop.xdigtop.i_logic_top.i_test.i_test_control.i_otp_wrapper.u_otpwrap_l3_top.u_otpwrap_l2_cpu.u_otpwrap_l1_jtag.otp_clk_reg" \
	"top_tb.th.i_dut_wrapper.xtop.xdigtop.i_logic_top.i_test.i_test_control.i_otp_wrapper.u_otpwrap_l3_top.u_otpwrap_l2_cpu.u_otpwrap_l1_jtag.shift_dr_re_syn_reg_0_" \
	"top_tb.th.i_dut_wrapper.xtop.xdigtop.i_logic_top.i_test.i_test_control.i_otp_wrapper.u_otpwrap_l3_top.u_otpwrap_l2_cpu.u_otpwrap_l1_jtag.shift_dr_synch_reg_0_" \
	"top_tb.th.i_dut_wrapper.xtop.xdigtop.i_logic_top.i_test.i_test_control.i_otp_wrapper.u_otpwrap_l3_top.u_otpwrap_l2_cpu.u_otpwrap_l1_jtag.start_read_synch_reg_0_" \
	"top_tb.th.i_dut_wrapper.xtop.xdigtop.i_logic_top.i_test.i_test_control.i_otp_wrapper.u_otpwrap_l3_top.u_otpwrap_l2_cpu.u_otpwrap_l1_jtag.*_synch_reg_0" \
	"top_tb.th.i_dut_wrapper.xtop.xdigtop.i_logic_top.i_test.i_test_control.i_otp_wrapper.u_otpwrap_l3_top.u_otpwrap_l2_cpu.u_otpwrap_l1_jtag.shift_dr_re_syn_reg_0_" \
	"top_tb.th.i_dut_wrapper.xtop.xdigtop.i_logic_top.i_test.i_test_control.i_otp_wrapper.u_otpwrap_l3_top.u_otpwrap_l2_cpu.u_otpwrap_l1_jtag.en_otpimp_synch_reg_0_" \
	"top_tb.th.i_dut_wrapper.xtop.xdigtop.i_logic_top.i_test.i_test_control.i_otp_wrapper.u_otpwrap_l3_top.u_otpwrap_l2_cpu.u_otpwrap_l1_jtag.start_prog_synch_reg_0_"
	"top_tb.th.i_dut_wrapper.xtop.xdigtop.i_logic_top.i_test.i_test_control.i_otp_wrapper.u_otpwrap_l3_top.u_otpwrap_l2_cpu.u_otpwrap_l1_jtag.ir_prog_clk_reg" \
	"top_tb.th.i_dut_wrapper.xtop.xdigtop.i_logic_top.i_test.i_test_control.i_otp_wrapper.u_otpwrap_l3_top.u_otpwrap_l2_cpu.u_otpwrap_l1_jtag.u_otpwrap_l0_atpg.gen_tsmc_u_otp4kx12.u_otp4kx12" \
	"top_tb.th.i_dut_wrapper.xtop.xdigtop.i_logic_top.i_data_storage.i_ram_wrapper_ecc_with_bist.utils_sram_with_bist_inst.utils_sram_bist_inst.march_22n_utils_sram_bist_march_inst.utils_sync_level_inst.i_utils_ff_re.q_reg" \
	"top_tb.th.i_dut_wrapper.xtop.xdigtop.i_logic_top.i_test.i_test_control.i_clock_switch.sel_1_s_reg" \
	"top_tb.th.i_dut_wrapper.xtop.xdigtop.i_logic_top.i_test.i_test_control.i_clock_switch.sel_2_s_reg" \
	"top_tb.th.i_dut_wrapper.xtop.xdigtop.i_logic_top.i_test.i_test_control.i_clock_switch.LOCKUP" \
	"top_tb.th.i_dut_wrapper.xtop.xdigtop.i_logic_top.i_test.i_test_control.i_otp_wrapper.u_otpwrap_l3_top.u_otpwrap_l2_cpu.u_otpwrap_l1_jtag.u_otp_ctrl.ir_otpbist_ctrl_clk_reg"
}


## anpassen der foreach Schleife in der Regel nicht nötig!

foreach searchpattern $searchpattern {
    puts "Instance matching $searchpattern..."
    set instances [search -instances $searchpattern]
    foreach instance $instances {
    tcheck $instance all -xgen -msg -disable -r
    puts "Disable timing check for: $instance"
    }
}
