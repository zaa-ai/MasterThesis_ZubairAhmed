# We don't want have infered Latches so upgrading the warning to an error.
set_message_info -stop_on -id {ELAB-395}

# If you do need to access this interface array in a consistent way across the RTL and the elaborated or synthesized design, then:
# Modify the SystemVerilog RTL to define interface arrays as [0:N-1] or [N-1:0] consistently throughout the design, and
# Set the hdlin_interface_port_downto application variable to false or true depending on whether the RTL array direction is
# upward or downward, respectively.
# For more information, see SolvNet article 2993652 ("How Does Elaboration Represent Arrays of Interfaces?") and SolvNet article
# 1694330 ("Naming of SystemVerilog Interface Array Ports").
set_app_var hdlin_interface_port_downto true
#set_app_var hdlin_reporting_level verbose
set_app_var hdlin_reporting_level {basic+fsm}
################################################################
# Set the optimization flow to hplp (high performance low power)
set OPTIMIZATION_FLOW "hplp"
# Set the register ungrouping file, will be sourced in dc_compile_settings.tcl
set REGISTER_UNGROUPING_FILE ../../edf_registers/ungroup.tcl

source user_tcl/dc_suppress_trivial_project_dependend_warnings.tcl
source $env(PROJECT_HOME)/scripts/misc/tcl/dc_suppress_trivial_messages.tcl

source user_tcl/common_setup.tcl

source -echo $env(PROJECT_HOME)/scripts/syn/tcl/dc/dc_setup_filenames.tcl

set DCRM_DCT_DEF_INPUT_FILE   digtop.def 
set DCRM_DCT_FLOORPLAN_INPUT_FILE ""
set DCRM_DCT_PHYSICAL_CONSTRAINTS_INPUT_FILE ""

source -echo $env(PROJECT_HOME)/scripts/syn/tcl/dc/dc_setup.tcl

#set hdlin_infer_fsm true
#set fsm_auto_inferring true
#set hdlin_failsafe_fsm true
#set hdlin_reporting_level basic+fsm
#set_app_var fsm_auto_inferring true
#set_app_var hdlin_infer_mux all

set AUTOREAD_EXCLUDE_LIST [readFromFile user_tcl/autoread_exclude_list]
source -echo $env(PROJECT_HOME)/scripts/syn/tcl/dc/dc_elab.tcl

source -echo $env(PROJECT_HOME)/scripts/syn/tcl/dc/dc_compile_settings.tcl
source -echo user_tcl/user_dc_compile_settings.tcl

source -echo $env(PROJECT_HOME)/scripts/syn/tcl/dc/dc_compile.tcl

# flatten small modules
foreach mod [list "pad_if_*"] {
    foreach_in_collection my_cells [get_cells -hier * -filter "ref_name =~ ${mod}"] {
    set mod_name [get_object_name $my_cells]
    puts "ungrouping $mod_name"
    ungroup $mod_name
  }
}

source -echo $env(PROJECT_HOME)/scripts/syn/tcl/dc/dc_dft_settings_compr.tcl
source -echo $env(PROJECT_HOME)/scripts/syn/tcl/dc/dc_dft_settings.tcl

source -echo $env(PROJECT_HOME)/scripts/syn/tcl/dc/dc_dft_build.tcl
source -echo $env(PROJECT_HOME)/scripts/syn/tcl/dc/dc_incr_compile.tcl

remove_unconnected_ports [get_cell -hier] -blast_buses
set old_design [current_design]
foreach_in_collection this_design [get_designs *] {
     current_design $this_design
     set leaf_cells [get_cells * -filter "@is_hierarchical!=true"]
     
     foreach_in_collection this_cell $leaf_cells {
            set output_pins [get_pins -of_objects $this_cell -filter "pin_direction==out"]
            if { [get_nets -of_object $output_pins] == ""} {
				puts [get_object_name $this_cell]
                  remove_cell $this_cell
            }
     }
}
current_design $old_design

source -echo $env(PROJECT_HOME)/scripts/syn/tcl/dc/dc_output.tcl
source -echo user_tcl/dc_output_dft.tcl
source -echo user_tcl/report.tcl

# Needed for pattern generation
source -echo create_nonDFT_signals_list.tcl

print_message_info

if {$env(QUIT) != 0} {
  exit
}

start_gui
