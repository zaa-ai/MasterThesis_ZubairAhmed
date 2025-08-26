##########################################################################################
# Version: M-2016.12-SP4 (July 17, 2017)
# Copyright (C) 2010-2017 Synopsys, Inc. All rights reserved.
##########################################################################################

puts "RM-Info: Running script [info script]\n"

# ELMOS
# source -echo ./rm_setup/icc_setup.tcl 

#######################################
####Outputs Script
#######################################

##Open Design
open_mw_cel $ICC_METAL_FILL_CEL -lib $MW_DESIGN_LIBRARY

# ELMOS
##Change Names
define_name_rules LVS -case_insensitive -max_length 128
change_names -rules verilog -hierarchy
change_names -rules LVS -hierarchy -verbose ;# Use this names for all

# ELMOS: patch time stamp to an instance name of the netlist
set id_fill [index_collection [get_flat_cells -all -filter "mask_layout_type == std_filler" *] 0]
set time_stamp [exec date +%Y%m%d_%H%M]
set ID "IDENT_${time_stamp}_${DESIGN_NAME}_$env(USER)"
set_name $id_fill -type cell -name $ID

# ELMOS
remove_route_guide -all
remove_placement_blockage -all

save_mw_cel -as $ICC_OUTPUTS_CEL 
close_mw_cel
open_mw_cel $ICC_OUTPUTS_CEL


##Verilog
if {$ICC_WRITE_FULL_CHIP_VERILOG} {
write_verilog -diode_ports -no_physical_only_cells $RESULTS_DIR/$DESIGN_NAME.output.v -macro_definition -wire_declaration

## For comparison with a Design Compiler netlist,the option -diode_ports is removed
write_verilog -no_physical_only_cells $RESULTS_DIR/$DESIGN_NAME.output.dc.v -macro_definition -wire_declaration

## For LVS use,the option -no_physical_only_cells is removed
write_verilog -diode_ports -pg $RESULTS_DIR/$DESIGN_NAME.output.pg.lvs.v -macro_definition -wire_declaration

} else {
write_verilog -diode_ports -no_physical_only_cells $RESULTS_DIR/$DESIGN_NAME.output.v -wire_declaration

## For comparison with a Design Compiler netlist,the option -diode_ports is removed
write_verilog -no_physical_only_cells $RESULTS_DIR/$DESIGN_NAME.output.dc.v -wire_declaration
}

## For LVS use,the option -no_physical_only_cells is removed
# ELMOS added -no_physical_only_cells and -force_output_references
# ELMOS changed $FILLER_CELL_METAL to $OUTPUT_REFERENCES which is set in icc_setup
write_verilog -diode_ports -pg -no_physical_only_cells -force_output_references $OUTPUT_REFERENCES $RESULTS_DIR/$DESIGN_NAME.output.pg.lvs.v -wire_declaration


## Add -output_net_name_for_tie option to write_verilog command
#  if the verilog file is to be used by "eco_netlist -by_verilog_file" command in eco_icc task

## For Prime Time use,to include DCAP cells for leakage power analysis, add the option -force_output_references
#  if {$ICC_WRITE_FULL_CHIP_VERILOG} {
#  write_verilog -diode_ports -no_physical_only_cells -force_output_references [list of your DCAP cells] $RESULTS_DIR/$DESIGN_NAME.output.pt.v -macro_definition
#  } else {
#  write_verilog -diode_ports -no_physical_only_cells -force_output_references [list of your DCAP cells] $RESULTS_DIR/$DESIGN_NAME.output.pt.v
#  }

##SDC
set_app_var write_sdc_output_lumped_net_capacitance false
set_app_var write_sdc_output_net_resistance false

   set cur_scenario [current_scenario]
   foreach scenario [all_active_scenarios] {
     current_scenario $scenario
     write_sdc $RESULTS_DIR/$DESIGN_NAME.$scenario.output.sdc
   };
   current_scenario $cur_scenario

extract_rc -coupling_cap
write_parasitics  -format SPEF -output $RESULTS_DIR/$DESIGN_NAME.output.spef
#write_parasitics  -format SBPF -output $RESULTS_DIR/$DESIGN_NAME.output.sbpf

##DEF
write_def -output  $RESULTS_DIR/$DESIGN_NAME.output.def
# ELMOS
exec gzip -f $RESULTS_DIR/$DESIGN_NAME.output.def &
#ELMOS
write_def -version 5.7 -rows_tracks_gcells -fixed -pins -blockages -specialnets  -vias -regions_groups -verbose -output $RESULTS_DIR/$DESIGN_NAME.output.syn.def
exec gzip -f $RESULTS_DIR/$DESIGN_NAME.output.syn.def &

###GDSII
##Set options - usually also include a mapping file (-map_layer)
##  set_write_stream_options \
#  -child_depth 99 \
#       -output_filling fill \
#       -output_outdated_fill \
#       -output_pin geometry \
#       -keep_data_type
#   write_stream -lib_name $MW_DESIGN_LIBRARY -format gds $RESULTS_DIR/$DESIGN_NAME.gds

if {$ICC_CREATE_MODEL } {
  save_mw_cel -as $DESIGN_NAME
  close_mw_cel
  open_mw_cel $DESIGN_NAME

  source -echo common_optimization_settings_icc.tcl
  source -echo common_placement_settings_icc.tcl
  source -echo common_post_cts_timing_settings.tcl
  source -echo common_route_si_settings_zrt_icc.tcl

  create_macro_fram 

  if {$ICC_FIX_ANTENNA} {
  ##create Antenna Info
    extract_zrt_hier_antenna_property -cell_name $DESIGN_NAME
  }

  create_block_abstraction
  save_mw_cel
  close_mw_cel 
}

puts "RM-Info: Completed script [info script]\n"

# ELMOS: removed, leave it to the main script if we want to exit the tool here
#exit

