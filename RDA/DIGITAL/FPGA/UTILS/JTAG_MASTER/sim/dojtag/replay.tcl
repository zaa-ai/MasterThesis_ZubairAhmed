# Begin_DVE_Session_Save_Info
# DVE full session
# Saved on Thu Dec 3 11:11:32 2020
# Designs open: 1
#   Sim: simv
# Toplevel windows open: 2
# 	TopLevel.1
# 	TopLevel.2
#   Source.1: tb
#   Wave.1: 37 signals
#   Group count = 6
#   Group xtap signal count = 77
#   Group TB signal count = 17
#   Group Group2 signal count = 7
#   Group TAP MASTER signal count = 6
#   Group TAP SLAVE signal count = 7
# End_DVE_Session_Save_Info

# DVE version: N-2017.12-SP2_Full64
# DVE build date: Jun  5 2018 21:29:11


#<Session mode="Full" path="/nfs/wrk.mfi/sim/dojtag/replay.tcl" type="Debug">

gui_set_loading_session_type Post
gui_continuetime_set

# Close design
if { [gui_sim_state -check active] } {
    gui_sim_terminate
}
gui_close_db -all
gui_expr_clear_all

# Close all windows
gui_close_window -type Console
gui_close_window -type Wave
gui_close_window -type Source
gui_close_window -type Schematic
gui_close_window -type Data
gui_close_window -type DriverLoad
gui_close_window -type List
gui_close_window -type Memory
gui_close_window -type HSPane
gui_close_window -type DLPane
gui_close_window -type Assertion
gui_close_window -type CovHier
gui_close_window -type CoverageTable
gui_close_window -type CoverageMap
gui_close_window -type CovDetail
gui_close_window -type Local
gui_close_window -type Stack
gui_close_window -type Watch
gui_close_window -type Group
gui_close_window -type Transaction



# Application preferences
gui_set_pref_value -key app_default_font -value {Helvetica,10,-1,5,50,0,0,0,0,0}
gui_src_preferences -tabstop 8 -maxbits 24 -windownumber 1
#<WindowLayout>

# DVE top-level session


# Create and position top-level window: TopLevel.1

if {![gui_exist_window -window TopLevel.1]} {
    set TopLevel.1 [ gui_create_window -type TopLevel \
       -icon $::env(DVE)/auxx/gui/images/toolbars/dvewin.xpm] 
} else { 
    set TopLevel.1 TopLevel.1
}
gui_show_window -window ${TopLevel.1} -show_state normal -rect {{1129 74} {1810 938}}

# ToolBar settings
gui_set_toolbar_attributes -toolbar {TimeOperations} -dock_state top
gui_set_toolbar_attributes -toolbar {TimeOperations} -offset 0
gui_show_toolbar -toolbar {TimeOperations}
gui_hide_toolbar -toolbar {&File}
gui_set_toolbar_attributes -toolbar {&Edit} -dock_state top
gui_set_toolbar_attributes -toolbar {&Edit} -offset 0
gui_show_toolbar -toolbar {&Edit}
gui_hide_toolbar -toolbar {CopyPaste}
gui_set_toolbar_attributes -toolbar {&Trace} -dock_state top
gui_set_toolbar_attributes -toolbar {&Trace} -offset 0
gui_show_toolbar -toolbar {&Trace}
gui_hide_toolbar -toolbar {TraceInstance}
gui_hide_toolbar -toolbar {BackTrace}
gui_set_toolbar_attributes -toolbar {&Scope} -dock_state top
gui_set_toolbar_attributes -toolbar {&Scope} -offset 0
gui_show_toolbar -toolbar {&Scope}
gui_set_toolbar_attributes -toolbar {&Window} -dock_state top
gui_set_toolbar_attributes -toolbar {&Window} -offset 0
gui_show_toolbar -toolbar {&Window}
gui_set_toolbar_attributes -toolbar {Signal} -dock_state top
gui_set_toolbar_attributes -toolbar {Signal} -offset 0
gui_show_toolbar -toolbar {Signal}
gui_set_toolbar_attributes -toolbar {Zoom} -dock_state top
gui_set_toolbar_attributes -toolbar {Zoom} -offset 0
gui_show_toolbar -toolbar {Zoom}
gui_set_toolbar_attributes -toolbar {Zoom And Pan History} -dock_state top
gui_set_toolbar_attributes -toolbar {Zoom And Pan History} -offset 0
gui_show_toolbar -toolbar {Zoom And Pan History}
gui_set_toolbar_attributes -toolbar {Grid} -dock_state top
gui_set_toolbar_attributes -toolbar {Grid} -offset 0
gui_show_toolbar -toolbar {Grid}
gui_set_toolbar_attributes -toolbar {Simulator} -dock_state top
gui_set_toolbar_attributes -toolbar {Simulator} -offset 0
gui_show_toolbar -toolbar {Simulator}
gui_set_toolbar_attributes -toolbar {Interactive Rewind} -dock_state top
gui_set_toolbar_attributes -toolbar {Interactive Rewind} -offset 0
gui_show_toolbar -toolbar {Interactive Rewind}
gui_set_toolbar_attributes -toolbar {Testbench} -dock_state top
gui_set_toolbar_attributes -toolbar {Testbench} -offset 0
gui_show_toolbar -toolbar {Testbench}

# End ToolBar settings

# Docked window settings
set HSPane.1 [gui_create_window -type HSPane -parent ${TopLevel.1} -dock_state left -dock_on_new_line true -dock_extent 300]
catch { set Hier.1 [gui_share_window -id ${HSPane.1} -type Hier] }
gui_set_window_pref_key -window ${HSPane.1} -key dock_width -value_type integer -value 300
gui_set_window_pref_key -window ${HSPane.1} -key dock_height -value_type integer -value 612
gui_set_window_pref_key -window ${HSPane.1} -key dock_offset -value_type integer -value 0
gui_update_layout -id ${HSPane.1} {{left 0} {top 0} {width 299} {height 303} {dock_state left} {dock_on_new_line true} {child_hier_colhier 173} {child_hier_coltype 120} {child_hier_colpd 0} {child_hier_col1 0} {child_hier_col2 1} {child_hier_col3 -1}}
set Console.1 [gui_create_window -type Console -parent ${TopLevel.1} -dock_state bottom -dock_on_new_line true -dock_extent 380]
gui_set_window_pref_key -window ${Console.1} -key dock_width -value_type integer -value 1860
gui_set_window_pref_key -window ${Console.1} -key dock_height -value_type integer -value 380
gui_set_window_pref_key -window ${Console.1} -key dock_offset -value_type integer -value 0
gui_update_layout -id ${Console.1} {{left 0} {top 0} {width 681} {height 379} {dock_state bottom} {dock_on_new_line true}}
#### Start - Readjusting docked view's offset / size
set dockAreaList { top left right bottom }
foreach dockArea $dockAreaList {
  set viewList [gui_ekki_get_window_ids -active_parent -dock_area $dockArea]
  foreach view $viewList {
      if {[lsearch -exact [gui_get_window_pref_keys -window $view] dock_width] != -1} {
        set dockWidth [gui_get_window_pref_value -window $view -key dock_width]
        set dockHeight [gui_get_window_pref_value -window $view -key dock_height]
        set offset [gui_get_window_pref_value -window $view -key dock_offset]
        if { [string equal "top" $dockArea] || [string equal "bottom" $dockArea]} {
          gui_set_window_attributes -window $view -dock_offset $offset -width $dockWidth
        } else {
          gui_set_window_attributes -window $view -dock_offset $offset -height $dockHeight
        }
      }
  }
}
#### End - Readjusting docked view's offset / size
gui_sync_global -id ${TopLevel.1} -option true

# MDI window settings
set Source.1 [gui_create_window -type {Source}  -parent ${TopLevel.1}]
gui_show_window -window ${Source.1} -show_state maximized
gui_update_layout -id ${Source.1} {{show_state maximized} {dock_state undocked} {dock_on_new_line false}}
set DLPane.1 [gui_create_window -type {DLPane}  -parent ${TopLevel.1}]
if {[gui_get_shared_view -id ${DLPane.1} -type Data] == {}} {
        set Data.1 [gui_share_window -id ${DLPane.1} -type Data]
} else {
        set Data.1  [gui_get_shared_view -id ${DLPane.1} -type Data]
}

gui_show_window -window ${DLPane.1} -show_state maximized
gui_update_layout -id ${DLPane.1} {{show_state maximized} {dock_state undocked} {dock_on_new_line false} {child_data_colvariable 210} {child_data_colvalue 49} {child_data_coltype 103} {child_data_col1 0} {child_data_col2 1} {child_data_col3 2}}

# End MDI window settings


# Create and position top-level window: TopLevel.2

if {![gui_exist_window -window TopLevel.2]} {
    set TopLevel.2 [ gui_create_window -type TopLevel \
       -icon $::env(DVE)/auxx/gui/images/toolbars/dvewin.xpm] 
} else { 
    set TopLevel.2 TopLevel.2
}
gui_show_window -window ${TopLevel.2} -show_state normal -rect {{0 23} {1919 1079}}

# ToolBar settings
gui_set_toolbar_attributes -toolbar {TimeOperations} -dock_state top
gui_set_toolbar_attributes -toolbar {TimeOperations} -offset 0
gui_show_toolbar -toolbar {TimeOperations}
gui_hide_toolbar -toolbar {&File}
gui_set_toolbar_attributes -toolbar {&Edit} -dock_state top
gui_set_toolbar_attributes -toolbar {&Edit} -offset 0
gui_show_toolbar -toolbar {&Edit}
gui_hide_toolbar -toolbar {CopyPaste}
gui_set_toolbar_attributes -toolbar {&Trace} -dock_state top
gui_set_toolbar_attributes -toolbar {&Trace} -offset 0
gui_show_toolbar -toolbar {&Trace}
gui_hide_toolbar -toolbar {TraceInstance}
gui_hide_toolbar -toolbar {BackTrace}
gui_set_toolbar_attributes -toolbar {&Scope} -dock_state top
gui_set_toolbar_attributes -toolbar {&Scope} -offset 0
gui_show_toolbar -toolbar {&Scope}
gui_set_toolbar_attributes -toolbar {&Window} -dock_state top
gui_set_toolbar_attributes -toolbar {&Window} -offset 0
gui_show_toolbar -toolbar {&Window}
gui_set_toolbar_attributes -toolbar {Signal} -dock_state top
gui_set_toolbar_attributes -toolbar {Signal} -offset 0
gui_show_toolbar -toolbar {Signal}
gui_set_toolbar_attributes -toolbar {Zoom} -dock_state top
gui_set_toolbar_attributes -toolbar {Zoom} -offset 0
gui_show_toolbar -toolbar {Zoom}
gui_set_toolbar_attributes -toolbar {Zoom And Pan History} -dock_state top
gui_set_toolbar_attributes -toolbar {Zoom And Pan History} -offset 0
gui_show_toolbar -toolbar {Zoom And Pan History}
gui_set_toolbar_attributes -toolbar {Grid} -dock_state top
gui_set_toolbar_attributes -toolbar {Grid} -offset 0
gui_show_toolbar -toolbar {Grid}
gui_set_toolbar_attributes -toolbar {Simulator} -dock_state top
gui_set_toolbar_attributes -toolbar {Simulator} -offset 0
gui_show_toolbar -toolbar {Simulator}
gui_set_toolbar_attributes -toolbar {Interactive Rewind} -dock_state top
gui_set_toolbar_attributes -toolbar {Interactive Rewind} -offset 0
gui_show_toolbar -toolbar {Interactive Rewind}
gui_set_toolbar_attributes -toolbar {Testbench} -dock_state top
gui_set_toolbar_attributes -toolbar {Testbench} -offset 0
gui_show_toolbar -toolbar {Testbench}

# End ToolBar settings

# Docked window settings
gui_sync_global -id ${TopLevel.2} -option true

# MDI window settings
set Wave.1 [gui_create_window -type {Wave}  -parent ${TopLevel.2}]
gui_show_window -window ${Wave.1} -show_state maximized
gui_update_layout -id ${Wave.1} {{show_state maximized} {dock_state undocked} {dock_on_new_line false} {child_wave_left 557} {child_wave_right 1357} {child_wave_colname 223} {child_wave_colvalue 330} {child_wave_col1 0} {child_wave_col2 1}}

# End MDI window settings

gui_set_env TOPLEVELS::TARGET_FRAME(Source) ${TopLevel.1}
gui_set_env TOPLEVELS::TARGET_FRAME(Schematic) ${TopLevel.1}
gui_set_env TOPLEVELS::TARGET_FRAME(PathSchematic) ${TopLevel.1}
gui_set_env TOPLEVELS::TARGET_FRAME(Wave) none
gui_set_env TOPLEVELS::TARGET_FRAME(List) none
gui_set_env TOPLEVELS::TARGET_FRAME(Memory) ${TopLevel.1}
gui_set_env TOPLEVELS::TARGET_FRAME(DriverLoad) none
gui_update_statusbar_target_frame ${TopLevel.1}
gui_update_statusbar_target_frame ${TopLevel.2}

#</WindowLayout>

#<Database>

# DVE Open design session: 

if { [llength [lindex [gui_get_db -design Sim] 0]] == 0 } {
gui_set_env SIMSETUP::SIMARGS {{-ucligui }}
gui_set_env SIMSETUP::SIMEXE {simv}
gui_set_env SIMSETUP::ALLOW_POLL {0}
if { ![gui_is_db_opened -db {simv}] } {
gui_sim_run Ucli -exe simv -args {-ucligui } -dir ../dojtag -nosource
}
}
if { ![gui_sim_state -check active] } {error "Simulator did not start correctly" error}
gui_set_precision 1ns
gui_set_time_units 1us
#</Database>

# DVE Global setting session: 


# Global: Breakpoints

# Global: Bus

# Global: Expressions

# Global: Signal Time Shift

# Global: Signal Compare

# Global: Signal Groups
gui_load_child_values {tb.xdojtag.xtapm}
gui_load_child_values {tb}
gui_load_child_values {tb.xdojtag}
gui_load_child_values {tb.xtap}


set _session_group_1 xtap
gui_sg_create "$_session_group_1"
set xtap "$_session_group_1"

gui_sg_addsignal -group "$_session_group_1" { tb.xtap.bypass_int tb.xtap.bypass_sel tb.xtap.bypass_so tb.xtap.capture_dr tb.xtap.capture_en_dr tb.xtap.capture_reg_dr tb.xtap.capture_reg_dr_msb tb.xtap.capture_reg_ir tb.xtap.capture_reg_ir_msb tb.xtap.clock_dr tb.xtap.clock_ir tb.xtap.data_in_int tb.xtap.data_in_ir tb.xtap.extest tb.xtap.fsm_rst tb.xtap.id tb.xtap.id_code_vec tb.xtap.id_sel tb.xtap.id_so tb.xtap.instr_rst tb.xtap.instr_so tb.xtap.instructions tb.xtap.man_num tb.xtap.man_num_vec_cnst tb.xtap.next_tap_state tb.xtap.nxt_fsm_rst tb.xtap.nxt_shift_dr tb.xtap.nxt_shift_ir tb.xtap.part tb.xtap.part_vec_cnst tb.xtap.samp_load tb.xtap.sentinel_val tb.xtap.shift_dr tb.xtap.shift_ir tb.xtap.so tb.xtap.sync_capture_en tb.xtap.sync_capture_ir tb.xtap.sync_mode tb.xtap.sync_update_dr tb.xtap.tap_state tb.xtap.tck tb.xtap.tck_n tb.xtap.tdi tb.xtap.tdo tb.xtap.tdo_en tb.xtap.tdo_temp tb.xtap.test tb.xtap.tms tb.xtap.trst_n tb.xtap.tst_mode tb.xtap.update_dr tb.xtap.update_ir tb.xtap.update_reg_ir tb.xtap.update_reg_ir_temp tb.xtap.update_reg_ir_temp_by tb.xtap.update_reg_ir_temp_n tb.xtap.version tb.xtap.version_vec_cnst tb.xtap.width tb.irdr tb.tick tb.ir tb.tdi tb.rstn tb.dr tb.shift_dr tb.tdo tb.soc tb.update_dr tb.eoc tb.clock_dr tb.tms tb.tck tb.clk tb.trstn tb.mem }
gui_set_radix -radix {decimal} -signals {Sim:tb.xtap.id}
gui_set_radix -radix {twosComplement} -signals {Sim:tb.xtap.id}
gui_set_radix -radix {decimal} -signals {Sim:tb.xtap.id_code_vec}
gui_set_radix -radix {unsigned} -signals {Sim:tb.xtap.id_code_vec}
gui_set_radix -radix {decimal} -signals {Sim:tb.xtap.man_num}
gui_set_radix -radix {twosComplement} -signals {Sim:tb.xtap.man_num}
gui_set_radix -radix {decimal} -signals {Sim:tb.xtap.man_num_vec_cnst}
gui_set_radix -radix {unsigned} -signals {Sim:tb.xtap.man_num_vec_cnst}
gui_set_radix -radix {decimal} -signals {Sim:tb.xtap.part}
gui_set_radix -radix {twosComplement} -signals {Sim:tb.xtap.part}
gui_set_radix -radix {decimal} -signals {Sim:tb.xtap.part_vec_cnst}
gui_set_radix -radix {unsigned} -signals {Sim:tb.xtap.part_vec_cnst}
gui_set_radix -radix {decimal} -signals {Sim:tb.xtap.sync_mode}
gui_set_radix -radix {twosComplement} -signals {Sim:tb.xtap.sync_mode}
gui_set_radix -radix {decimal} -signals {Sim:tb.xtap.tst_mode}
gui_set_radix -radix {twosComplement} -signals {Sim:tb.xtap.tst_mode}
gui_set_radix -radix {decimal} -signals {Sim:tb.xtap.version}
gui_set_radix -radix {twosComplement} -signals {Sim:tb.xtap.version}
gui_set_radix -radix {decimal} -signals {Sim:tb.xtap.version_vec_cnst}
gui_set_radix -radix {unsigned} -signals {Sim:tb.xtap.version_vec_cnst}
gui_set_radix -radix {decimal} -signals {Sim:tb.xtap.width}
gui_set_radix -radix {twosComplement} -signals {Sim:tb.xtap.width}

set _session_group_2 $_session_group_1|
append _session_group_2 tb
gui_sg_create "$_session_group_2"
set xtap|tb "$_session_group_2"

gui_sg_addsignal -group "$_session_group_2" { {tb.unnamed$$_0.unnamed$$_1} {tb.unnamed$$_0.unnamed$$_2} tb.irdr tb.tick tb.ir tb.tdi tb.rstn tb.dr tb.shift_dr tb.tdo tb.soc tb.update_dr tb.eoc tb.clock_dr tb.tms tb.tck tb.clk tb.trstn tb.mem }

set _session_group_3 TB
gui_sg_create "$_session_group_3"
set TB "$_session_group_3"

gui_sg_addsignal -group "$_session_group_3" { tb.rstn tb.clk tb.trstn tb.irdr tb.tick tb.ir tb.tdi tb.dr tb.tdo tb.soc tb.update_dr tb.shift_dr tb.eoc tb.clock_dr tb.tms tb.tck tb.mem }

set _session_group_4 Group2
gui_sg_create "$_session_group_4"
set Group2 "$_session_group_4"

gui_sg_addsignal -group "$_session_group_4" { tb.xdojtag.cs tb.xdojtag.sel tb.xdojtag.tap_soc tb.xdojtag.tap_eoc tb.xdojtag.tms tb.xdojtag.tck tb.xdojtag.irdr }

set _session_group_5 {TAP MASTER}
gui_sg_create "$_session_group_5"
set {TAP MASTER} "$_session_group_5"

gui_sg_addsignal -group "$_session_group_5" { tb.xdojtag.xtapm.cs tb.xdojtag.xtapm.tms tb.xdojtag.xtapm.tck tb.xdojtag.xtapm.tdi tb.xdojtag.xtapm.ir tb.xdojtag.xtapm.dr }

set _session_group_6 {TAP SLAVE}
gui_sg_create "$_session_group_6"
set {TAP SLAVE} "$_session_group_6"

gui_sg_addsignal -group "$_session_group_6" { tb.xtap.test tb.xtap.trst_n tb.xtap.tap_state tb.xtap.tck tb.xtap.tms tb.xtap.shift_ir tb.xtap.update_ir }

# Global: Highlighting

# Global: Stack
gui_change_stack_mode -mode list

# Post database loading setting...

# Restore C1 time
gui_set_time -C1_only 121



# Save global setting...

# Wave/List view global setting
gui_cov_show_value -switch false

# Close all empty TopLevel windows
foreach __top [gui_ekki_get_window_ids -type TopLevel] {
    if { [llength [gui_ekki_get_window_ids -parent $__top]] == 0} {
        gui_close_window -window $__top
    }
}
gui_set_loading_session_type noSession
# DVE View/pane content session: 


# Hier 'Hier.1'
gui_show_window -window ${Hier.1}
gui_list_set_filter -id ${Hier.1} -list { {Package 1} {All 0} {Process 1} {VirtPowSwitch 0} {UnnamedProcess 1} {UDP 0} {Function 1} {Block 1} {SrsnAndSpaCell 0} {OVA Unit 1} {LeafScCell 1} {LeafVlgCell 1} {Interface 1} {LeafVhdCell 1} {$unit 1} {NamedBlock 1} {Task 1} {VlgPackage 1} {ClassDef 1} {VirtIsoCell 0} }
gui_list_set_filter -id ${Hier.1} -text {*}
gui_hier_list_init -id ${Hier.1}
gui_change_design -id ${Hier.1} -design Sim
catch {gui_list_expand -id ${Hier.1} tb}
catch {gui_list_select -id ${Hier.1} {tb.xtap}}
gui_view_scroll -id ${Hier.1} -vertical -set 0
gui_view_scroll -id ${Hier.1} -horizontal -set 0

# Source 'Source.1'
gui_src_value_annotate -id ${Source.1} -switch false
gui_set_env TOGGLE::VALUEANNOTATE 0
gui_open_source -id ${Source.1}  -replace -active tb tb.sv
gui_view_scroll -id ${Source.1} -vertical -set 16
gui_src_set_reusable -id ${Source.1}

# Data 'Data.1'
gui_list_set_filter -id ${Data.1} -list { {Buffer 1} {Input 1} {Others 1} {Linkage 1} {Output 1} {LowPower 1} {Parameter 1} {All 1} {Aggregate 1} {LibBaseMember 1} {Event 1} {Assertion 1} {Constant 1} {Interface 1} {BaseMembers 1} {Signal 1} {$unit 1} {Inout 1} {Variable 1} }
gui_list_set_filter -id ${Data.1} -text {*}
gui_list_show_data -id ${Data.1} {tb.xtap}
gui_show_window -window ${Data.1}
catch { gui_list_select -id ${Data.1} {tb.xtap.test }}
gui_view_scroll -id ${Data.1} -vertical -set 780
gui_view_scroll -id ${Data.1} -horizontal -set 0
gui_view_scroll -id ${Hier.1} -vertical -set 0
gui_view_scroll -id ${Hier.1} -horizontal -set 0

# View 'Wave.1'
gui_wv_sync -id ${Wave.1} -switch false
set groupExD [gui_get_pref_value -category Wave -key exclusiveSG]
gui_set_pref_value -category Wave -key exclusiveSG -value {false}
set origWaveHeight [gui_get_pref_value -category Wave -key waveRowHeight]
gui_list_set_height -id Wave -height 25
set origGroupCreationState [gui_list_create_group_when_add -wave]
gui_list_create_group_when_add -wave -disable
gui_marker_set_ref -id ${Wave.1}  C1
gui_wv_zoom_timerange -id ${Wave.1} 0 1000
gui_list_add_group -id ${Wave.1} -after {New Group} {TB}
gui_list_add_group -id ${Wave.1} -after {New Group} {Group2}
gui_list_add_group -id ${Wave.1} -after {New Group} {{TAP MASTER}}
gui_list_add_group -id ${Wave.1} -after {New Group} {{TAP SLAVE}}
gui_list_collapse -id ${Wave.1} Group2
gui_seek_criteria -id ${Wave.1} {Any Edge}



gui_set_env TOGGLE::DEFAULT_WAVE_WINDOW ${Wave.1}
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
gui_list_set_insertion_bar  -id ${Wave.1} -group TB  -item tb.shift_dr -position below

gui_marker_move -id ${Wave.1} {C1} 121
gui_view_scroll -id ${Wave.1} -vertical -set 41
gui_show_grid -id ${Wave.1} -enable false
# Restore toplevel window zorder
# The toplevel window could be closed if it has no view/pane
if {[gui_exist_window -window ${TopLevel.1}]} {
	gui_set_active_window -window ${TopLevel.1}
	gui_set_active_window -window ${DLPane.1}
	gui_set_active_window -window ${Console.1}
}
if {[gui_exist_window -window ${TopLevel.2}]} {
	gui_set_active_window -window ${TopLevel.2}
	gui_set_active_window -window ${Wave.1}
}
#</Session>

