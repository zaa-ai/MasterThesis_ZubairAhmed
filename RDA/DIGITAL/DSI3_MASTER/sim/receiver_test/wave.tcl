source dump.tcl
# Begin_DVE_Session_Save_Info
# DVE view(Wave.1 ) session
# Saved on Fri Sep 7 12:03:02 2018
# Toplevel windows open: 2
# 	TopLevel.1
# 	TopLevel.2
#   Wave.1: 61 signals
# End_DVE_Session_Save_Info

# DVE version: M-2017.03-SP2-9_Full64
# DVE build date: Jun 16 2018 20:38:50


#<Session mode="View" path="/nfs/wrk.jvoi/projekte/52142/m52142b/DIGITAL/unit_tests/spi_test_suite/wave.tcl" type="Debug">

#<Database>

gui_set_time_units 1ps
#</Database>

# DVE View/pane content session: 

# Begin_DVE_Session_Save_Info (Wave.1)
# DVE wave signals session
# Saved on Fri Sep 7 12:03:02 2018
# 61 signals
# End_DVE_Session_Save_Info

# DVE version: M-2017.03-SP2-9_Full64
# DVE build date: Jun 16 2018 20:38:50


#Add ncecessay scopes

gui_set_time_units 1ps

set _wave_session_group_1 spi_ut
if {[gui_sg_is_group -name "$_wave_session_group_1"]} {
    set _wave_session_group_1 [gui_sg_generate_new_name]
}
set Group1 "$_wave_session_group_1"

gui_sg_addsignal -group "$_wave_session_group_1" { {Sim:testrunner.spi_ts.spi_ut.clock_period_half} {Sim:testrunner.spi_ts.spi_ut.o_elip_out} {Sim:testrunner.spi_ts.spi_ut.o_spi_interrupt} {Sim:testrunner.spi_ts.spi_ut.o_spi_interrupt_mutec} {Sim:testrunner.spi_ts.spi_ut.spi_clock_period_half} }
gui_sg_set_analog_property  -group "$_wave_session_group_1" -color {#ff00ff}  -pos -1 -origGroup {}  {Sim:testrunner.spi_ts.spi_ut.clock_period_half}
gui_sg_set_analog_property  -group "$_wave_session_group_1" -color {#00ffff}  -pos -1 -origGroup {}  {Sim:testrunner.spi_ts.spi_ut.spi_clock_period_half}

set _wave_session_group_2 $_wave_session_group_1|
append _wave_session_group_2 my_spi_1
set spi_ut|my_spi_1 "$_wave_session_group_2"

gui_sg_addsignal -group "$_wave_session_group_2" { {Sim:testrunner.spi_ts.spi_ut.my_spi.clk_rst} {Sim:testrunner.spi_ts.spi_ut.my_spi.dsi3_status} {Sim:testrunner.spi_ts.spi_ut.my_spi.elip} {Sim:testrunner.spi_ts.spi_ut.my_spi.elip_out_crc} {Sim:testrunner.spi_ts.spi_ut.my_spi.elip_spi_intern_registers} {Sim:testrunner.spi_ts.spi_ut.my_spi.elip_spi_registers} {Sim:testrunner.spi_ts.spi_ut.my_spi.elip_spi_status_word} {Sim:testrunner.spi_ts.spi_ut.my_spi.i_clkref_ok} {Sim:testrunner.spi_ts.spi_ut.my_spi.i_ot} {Sim:testrunner.spi_ts.spi_ut.my_spi.i_reset_registers_sync_n} {Sim:testrunner.spi_ts.spi_ut.my_spi.i_vccuv} {Sim:testrunner.spi_ts.spi_ut.my_spi.new_data} {Sim:testrunner.spi_ts.spi_ut.my_spi.new_data_nxt} {Sim:testrunner.spi_ts.spi_ut.my_spi.o_elip_out} {Sim:testrunner.spi_ts.spi_ut.my_spi.o_spi_interrupt} {Sim:testrunner.spi_ts.spi_ut.my_spi.o_spi_interrupt_mutec} {Sim:testrunner.spi_ts.spi_ut.my_spi.reset_fifo} {Sim:testrunner.spi_ts.spi_ut.my_spi.reset_fifo_synced} {Sim:testrunner.spi_ts.spi_ut.my_spi.rx_data} {Sim:testrunner.spi_ts.spi_ut.my_spi.rxd_valid} {Sim:testrunner.spi_ts.spi_ut.my_spi.rxd_valid_sync} {Sim:testrunner.spi_ts.spi_ut.my_spi.spi_i} {Sim:testrunner.spi_ts.spi_ut.my_spi.tx_data} {Sim:testrunner.spi_ts.spi_ut.my_spi.txd_en_clear} {Sim:testrunner.spi_ts.spi_ut.my_spi.txd_en_clear_rising_sync} {Sim:testrunner.spi_ts.spi_ut.my_spi.txd_en_sync} {Sim:testrunner.spi_ts.spi_ut.my_spi.txd_request} {Sim:testrunner.spi_ts.spi_ut.my_spi.i_spi_core.i_status_word} }

set _wave_session_group_3 $_wave_session_group_1|
append _wave_session_group_3 Register_ut
set spi_ut|Register_ut "$_wave_session_group_3"

gui_sg_addsignal -group "$_wave_session_group_3" { {Sim:testrunner.spi_ts.spi_ut.my_spi.i_IC_Status_Word_Register.IC_Status_Word_Register_STATUS_WORD} {Sim:testrunner.spi_ts.spi_ut.my_spi.i_SPI_Intern_Registers.SPI_Intern_Registers_SPI_IRQ_STAT_SHADOW} {Sim:testrunner.spi_ts.spi_ut.my_spi.i_SPI_Intern_Registers.SPI_Intern_Registers_SPI_RX_DATA} {Sim:testrunner.spi_ts.spi_ut.my_spi.i_SPI_Intern_Registers.SPI_Intern_Registers_SPI_STAT} {Sim:testrunner.spi_ts.spi_ut.my_spi.i_SPI_Intern_Registers.SPI_Intern_Registers_SPI_TX_DATA} {Sim:testrunner.spi_ts.spi_ut.my_spi.i_SPI_registers.SPI_registers_SPI_IRQ_EN} {Sim:testrunner.spi_ts.spi_ut.my_spi.i_SPI_registers.SPI_registers_SPI_IRQ_STAT} {Sim:testrunner.spi_ts.spi_ut.my_spi.i_spi_crc.i_SPI_CRC_module.SPI_CRC_module_SPI_CRC} {Sim:testrunner.spi_ts.spi_ut.my_spi.i_spi_crc.i_SPI_CRC_module.SPI_CRC_module_SPI_CRC_DATA} }

gui_sg_move "$_wave_session_group_3" -after "$_wave_session_group_1" -pos 1 

set _wave_session_group_4 SPI_IRQ_TEST
if {[gui_sg_is_group -name "$_wave_session_group_4"]} {
    set _wave_session_group_4 [gui_sg_generate_new_name]
}
set Group2 "$_wave_session_group_4"

gui_sg_addsignal -group "$_wave_session_group_4" { {Sim:testrunner.spi_ts.spi_irq.o_spi_interrupt} {Sim:testrunner.spi_ts.spi_irq.o_spi_interrupt_mutec} {Sim:testrunner.spi_ts.spi_irq.my_spi.clk_rst} {Sim:testrunner.spi_ts.spi_irq.my_spi.elip} {Sim:testrunner.spi_ts.spi_irq.my_spi.o_elip_out} {Sim:testrunner.spi_ts.spi_irq.my_spi.spi_i} {Sim:testrunner.spi_ts.spi_irq.my_spi.i_SPI_Intern_Registers.SPI_Intern_Registers_SPI_IRQ_STAT_SHADOW} {Sim:testrunner.spi_ts.spi_irq.my_spi.i_SPI_Intern_Registers.SPI_Intern_Registers_SPI_RX_DATA} {Sim:testrunner.spi_ts.spi_irq.my_spi.i_SPI_Intern_Registers.SPI_Intern_Registers_SPI_STAT} {Sim:testrunner.spi_ts.spi_irq.my_spi.i_SPI_Intern_Registers.SPI_Intern_Registers_SPI_TX_DATA} {Sim:testrunner.spi_ts.spi_irq.my_spi.i_SPI_registers.SPI_registers_SPI_IRQ_EN} {Sim:testrunner.spi_ts.spi_irq.my_spi.i_SPI_registers.SPI_registers_SPI_IRQ_STAT} }

set _wave_session_group_5 {DSI CRC test}
if {[gui_sg_is_group -name "$_wave_session_group_5"]} {
    set _wave_session_group_5 [gui_sg_generate_new_name]
}
set Group3 "$_wave_session_group_5"

gui_sg_addsignal -group "$_wave_session_group_5" { {Sim:testrunner.spi_ts.spi_ct.my_spi.i_dsi3_crc_parallel.i_CRC_module_registers.CRC_module_registers_CRC} {Sim:testrunner.spi_ts.spi_ct.my_spi.i_dsi3_crc_parallel.i_CRC_module_registers.CRC_module_registers_CRC_DATA} {Sim:testrunner.spi_ts.spi_ct.my_spi.i_dsi3_crc_parallel.crc} {Sim:testrunner.spi_ts.spi_ct.my_spi.i_dsi3_crc_parallel.do_calculate} {Sim:testrunner.spi_ts.spi_ct.my_spi.i_dsi3_crc_parallel.elip} {Sim:testrunner.spi_ts.spi_ct.my_spi.i_dsi3_crc_parallel.o_elip_out_crc} {Sim:testrunner.spi_ts.spi_ct.my_spi.i_dsi3_crc_parallel.clk_rst} }
gui_set_radix -radix enum -signals {Sim:testrunner.spi_ts.spi_ct.my_spi.i_dsi3_crc_parallel.crc}
if {![info exists useOldWindow]} { 
	set useOldWindow true
}
if {$useOldWindow && [string first "Wave" [gui_get_current_window -view]]==0} { 
	set Wave.1 [gui_get_current_window -view] 
} else {
	set Wave.1 [lindex [gui_get_window_ids -type Wave] 0]
if {[string first "Wave" ${Wave.1}]!=0} {
gui_open_window Wave
set Wave.1 [ gui_get_current_window -view ]
}
}

set groupExD [gui_get_pref_value -category Wave -key exclusiveSG]
gui_set_pref_value -category Wave -key exclusiveSG -value {false}
set origWaveHeight [gui_get_pref_value -category Wave -key waveRowHeight]
gui_list_set_height -id Wave -height 25
set origGroupCreationState [gui_list_create_group_when_add -wave]
gui_list_create_group_when_add -wave -disable
gui_marker_create -id ${Wave.1} C2 387287913
gui_marker_set_ref -id ${Wave.1}  C1
gui_wv_zoom_timerange -id ${Wave.1} 712969232 713072440
gui_list_add_group -id ${Wave.1} -after {New Group} [list ${Group1}]
gui_list_add_group -id ${Wave.1}  -after ${Group1} [list ${spi_ut|my_spi_1}]
gui_list_add_group -id ${Wave.1} -after spi_ut|my_spi_1 [list ${spi_ut|Register_ut}]
gui_list_add_group -id ${Wave.1} -after {New Group} [list ${Group2}]
gui_list_add_group -id ${Wave.1} -after {New Group} [list ${Group3}]
gui_list_collapse -id ${Wave.1} ${Group1}
gui_list_collapse -id ${Wave.1} ${Group2}
gui_list_collapse -id ${Wave.1} ${Group3}
gui_seek_criteria -id ${Wave.1} {Any Edge}

gui_set_analog_wave_options -id ${Wave.1} -name Sim:testrunner.spi_ts.spi_ut.clock_period_half -mark_samples 0 -mark_sample_shape Cross -mark_sample_size 3 -yrange auto -ymin 27777 -ymax 27777 -yscale lin -yaxis_left 1 -yaxis_right 0
gui_set_analog_wave_options -id ${Wave.1} -name Sim:testrunner.spi_ts.spi_ut.spi_clock_period_half -mark_samples 0 -mark_sample_shape Cross -mark_sample_size 3 -yrange auto -ymin 250000 -ymax 250000 -yscale lin -yaxis_left 1 -yaxis_right 0

gui_set_pref_value -category Wave -key exclusiveSG -value $groupExD
gui_list_set_height -id Wave -height $origWaveHeight
if {$origGroupCreationState} {
	gui_list_create_group_when_add -wave -enable
}
if { $groupExD } {
 gui_msg_report -code DVWW028
}
gui_list_set_filter -id ${Wave.1} -list { {Buffer 1} {Input 1} {Others 1} {Linkage 1} {Output 1} {Parameter 1} {All 1} {Aggregate 1} {LibBaseMember 1} {Event 1} {Assertion 1} {Constant 1} {Interface 1} {BaseMembers 1} {Signal 1} {$unit 1} {Inout 1} {Variable 1} }
gui_list_set_filter -id ${Wave.1} -text {*}
gui_list_set_insertion_bar  -id ${Wave.1} -group ${Group3}  -position in

gui_marker_move -id ${Wave.1} {C1} 713780461
gui_view_scroll -id ${Wave.1} -vertical -set 0
gui_show_grid -id ${Wave.1} -enable false
#</Session>

