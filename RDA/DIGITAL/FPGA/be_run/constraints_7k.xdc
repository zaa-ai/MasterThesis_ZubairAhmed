
create_clock -period  10.000 -name clk100 -waveform {0.000  5.000} [get_ports CLK_100_P]
create_clock -period 100.000 -name swclk  -waveform {0.000 50.000} [get_ports DBG_SWCLK]

create_clock -period 100.000 -name wdog_clk    -waveform {0.000 50.000} [get_pins bufg_clk_wdog/O]
create_clock -period  12.500 -name clk_sys_osc -waveform {0.000 6.250} [get_pins clk_wiz_multiple_clk_inst/mmcm_adv_inst/CLKOUT3]
create_clock -period  15.200 -name clk_adc_if  -waveform {0.000 7.600} [get_pins clk_wiz_multiple_clk_inst/mmcm_adv_inst/CLKOUT2]

create_generated_clock -name clk_bus -source [get_pins clk_wiz_multiple_clk_inst/mmcm_adv_inst/CLKOUT3] -edges {1 3 5} -add -master_clock clk_sys_osc [get_pins bufg_clk_sys_osc/O]

set_clock_groups -name async_groups -asynchronous -group clk100 -group {clk_sys_osc clk_bus} -group {wdog_clk} -group {swclk} -group {clk_adc_if}

set_false_path -to   [get_pins  -hierarchical -filter { NAME =~  "*i_utils_sync_ff_re*/q_reg/D" }]
set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*por_ff*" }]
set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*nrst_core_reg*" }]

# suppress warning: WARNING: [Timing 38-172] LUT was found on clock network. Both rising/falling clock edges are propagated from LUT output pin. 
#set_clock_sense -positive digital_inst/core_iomux_inst/core_inst/standby_logic_inst/standby_gate_clk_sys_inst/utils_clk_gate_ff_inst/sync_nres_hold_ffs[0].sync_res_hold[0]_i_7/O


#cpu_core_sys_inst/imem_shell_32_imem0_inst/gen_sfl.sfl_ctrl_inst/sfl_scan_shell_inst/gen.sfl_wrapper_inst/sfl_xsram_inst/sfl_xsram_*_inst/bank*/CLKARDCLK
set_multicycle_path -from [get_pins  -hierarchical -filter { NAME =~ "*sfl_xsram_*_inst/bank*/CLKARDCLK" }] 2
set_multicycle_path -from [get_pins  -hierarchical -filter { NAME =~ "*sfl_xsram_*_inst/bank*/CLKARDCLK" }] -hold 1


