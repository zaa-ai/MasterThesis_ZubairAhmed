
################################################################################
# common_placement_settings_icc.tcl
################################################################################

# TODO: these settings are not stored in database
set_app_var timing_enable_non_sequential_checks true
set_app_var timing_enable_preset_clear_arcs true

#set_lib_cell_spacing_label -names A -right_lib_cells [get_physical_lib_cell tcb018gbwp7t/*] -left_lib_cells [get_physical_lib_cell tcb018gbwp7t/*]
#set_spacing_label_rule -labels {A A} {1 3}

################################################################################
# common_cts_settings_icc.tcl
################################################################################

# useful in multivoltage designs 
#set_clock_tree_exceptions -dont_buffer_nets [get_nets [get_object_name [get_cells -hier -filter "ref_name == sram4096x16_iso_nl"]]/CLK]
#set_clock_tree_exceptions -dont_buffer_nets [get_nets [get_object_name [get_cells -hier -filter "ref_name == sram8192x16_iso_nl"]]/CLK]
#set_clock_tree_exceptions -dont_buffer_nets [get_nets [get_object_name [get_cells -hier -filter "ref_name == sram8192x32_iso_nl"]]/CLK]
#foreach_in_collection cell [get_flat_cells -of_objects [get_cells -hier pure_and_CLK_inst]] {
#  set_clock_tree_exceptions -stop_pins [get_pins [get_object_name $cell]/A]
#}

set_clock_tree_optimization_options -relax_insertion_delay true

set_clock_tree_options -target_skew 1
set_clock_tree_options -max_transition 3
set_clock_tree_options -leaf_max_transition 1

# set exclude pins on all gating FFs, to avoid balancing with other sequential cells (why, no need for this? (leads to hold violations due to unbalanced clock tree))
#set clk_gate_cells [get_flat_cells -of_objects [get_cells -hierarchical -filter "ref_name =~ utils_clk_gate_*" *]]
#set clk_pins       [get_flat_pins -of_objects $clk_gate_cells -filter "full_name =~ */neg_clk_e_reg/CPN"]
#set_clock_tree_exceptions -exclude_pins $clk_pins
#set_clock_tree_exceptions -exclude_pins [get_flat_pins core_iomux_inst/core_inst/standby_logic_inst/standby_gate_clk_sys_inst/osc_pd_reg/CPN]

# set exclude pins on gclock FFs, to avoid impossible-to-balance situation due to clock defined in another mode (scan)
#set_clock_tree_exceptions -exclude_pins [get_flat_pins */sys_clk_divider_inst/clk24_div_reg/ff_inst/CP]

# useful to fix antenna violations on clk pin of sram
#if {[get_flat_cells */sram_clk_buf] != ""} {
#  set sram_clk_net [get_nets -of_objects [get_flat_pins */gen_sram_sram_inst/CLK]]
#  set_clock_tree_exceptions -dont_buffer_nets $sram_clk_net
#  set_net_routing_layer_constraints -min_layer_name METAL1 -max_layer_name METAL2 $sram_clk_net
#}

################################################################################
# common_route_si_settings_zrt_icc.tcl
################################################################################

#set_droute_options -name dropVia1InsideM1Pin -value 1
#set_route_zrt_common_options -connect_within_pins_by_layer_name {{METAL1 via_wire_standard_cell_pins}}
#set_route_zrt_common_options -global_min_layer_mode allow_pin_connection
#set_route_zrt_common_options -net_min_layer_mode allow_pin_connection
#set_route_zrt_common_options -number_of_vias_under_global_min_layer 1
#set_route_zrt_common_options -number_of_vias_under_net_min_layer 2
#set_route_zrt_common_options -connect_within_pins_by_layer_name {METAL1 via_wire_all_pins}

set_route_zrt_detail_options -default_port_external_gate_size 0.0
#set_route_zrt_detail_options -repair_shorts_over_macros_effort_level high
set_droute_options -name wideMacroPinAsFatWire -value 1
set_preferred_routing_direction -layers METAL5 -direction horizontal
