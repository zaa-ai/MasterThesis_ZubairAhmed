# Additional settings before first compile_ultra

set_clock_gating_style -num_stages 1 -minimum_bitwidth 3 -neg integrated  -pos integrated -control_signal scan_enable -control_point before

set_app_var compile_clock_gating_through_hierarchy true
set_app_var timing_separate_clock_gating_group true
set_app_var power_cg_physically_aware_cg true
set_auto_disable_drc_nets -on_clock_network true


set_app_var fsm_auto_inferring true
set_app_var fsm_enable_state_minimization true

#Size only for scan regs to not remove these while optimize
set_size_only [get_flat_cells *_SCAN*_reg*] true
uniquify
# For better test coverage
set_size_only [get_cells i_pad_mux_test_*/test_reg_reg] true

#Enable these to honor the -add option in sdc whith create_clock
set_app_var timing_enable_multiple_clocks_per_reg true 

#stop propagation of clocks thorough pad_mux_test instances
set_clock_sense -logical_stop_propagation -clocks [all_clocks] [get_pins -of_objects [get_cells i_pad_mux_test*/*]]

# Prevent assignment statements in the Verilog netlist.
set_fix_multiple_port_nets -all -buffer_constants

set_app_var compile_isolate_crc_logic true
set_app_var compile_seqmap_identify_shift_registers true
set_app_var compile_seqmap_enable_output_inversion true

source $REGISTER_UNGROUPING_FILE

uniquify -dont_skip_empty_designs
remove_unconnected_ports -blast [get_cell -hier ]
set_app_var compile_enable_constant_propagation_with_no_boundary_opt false

identify_clock_gating
