##########################################################################################
# Version: M-2016.12-SP4 (July 17, 2017)
# Copyright (C) 2010-2017 Synopsys, Inc. All rights reserved.
##########################################################################################

puts "RM-Info: Running script [info script]\n"

# ELMOS
# source -echo ./rm_setup/icc_setup.tcl 

############################################
## route_opt_icc: Post Route optimization ##
############################################

open_mw_lib $MW_DESIGN_LIBRARY
redirect /dev/null "remove_mw_cel -version_kept 0 ${ICC_ROUTE_OPT_CEL}"
copy_mw_cel -from $ICC_ROUTE_CEL -to $ICC_ROUTE_OPT_CEL

## TIO setup for route_opt command
if {$ICC_IMPLEMENTATION_PHASE == "top"} {
  ## Copy block CELs to current library for interface optimization, 
  #  if ICC_TIO_OPTIMIZE_BLOCK_INTERFACE is enabled, ICC_TIO_BLOCK_LIST not empty, and host options are specified 
  if {$ICC_TIO_OPTIMIZE_BLOCK_INTERFACE && $ICC_TIO_BLOCK_LIST != "" && $ICC_TIO_HOST_OPTION != ""} {
    foreach block $ICC_TIO_BLOCK_LIST {
    copy_mw_cel -from_lib ../$block/lib_$block -from $block 
    }
  }
}

open_mw_cel $ICC_ROUTE_OPT_CEL



source -echo common_optimization_settings_icc.tcl
source -echo common_placement_settings_icc.tcl
source -echo common_post_cts_timing_settings.tcl

## Load the route and si settings
source -echo common_route_si_settings_zrt_icc.tcl

##Source Concurrent Clock and Data Options
source -echo common_concurrent_clock_and_data_settings_icc.tcl


  if {$ICC_MCMM_ROUTE_OPT_SCENARIOS != ""} {
    set_active_scenarios $ICC_MCMM_ROUTE_OPT_SCENARIOS
  } else {
    set_active_scenarios [lminus [all_scenarios] [get_scenarios -setup false -hold false -cts_mode true]]
    ## Note: CTS only scenarios (get_scenarios -setup false -hold false -cts_mode true) are made inactive by RM during optimizations
  }

  ## If you add additional scenarios after clock_opt_cts_icc step, use the following command to propagate all clock sources for active scenarios :
  #  propagate_all_clocks


##############################
## RP : Relative Placement  ##     
##############################
## Ensuring that the RP cells are not changed during route_opt
#set_rp_group_options [all_rp_groups] -route_opt_option fixed_placement
#set_rp_group_options [all_rp_groups] -route_opt_option "size_only"


if { [check_error -verbose] != 0} { echo "RM-Error, flagging ..." }
## start the post route optimization
set_app_var compile_instance_name_prefix icc_route_opt
if {$ICC_SANITY_CHECK} {
  check_physical_design -stage pre_route_opt -no_display -output check_physical_design.pre_route_opt
}

if { [check_error -verbose] != 0} { echo "RM-Error, flagging ..." }

if {$ICC_ENABLE_CHECKPOINT} {
echo "RM-Info : Please ensure there's enough disk space before enabling the set_checkpoint_strategy feature."
set_checkpoint_strategy -enable -overwrite
# The -overwrite option is used by default. Remove it if needed.
}

# To enable cell pre-sizing as a first step in route_opt crosstalk reduction,
# set the following variable to TRUE (default is FALSE):
# set_app_var routeopt_xtalk_reduction_cell_sizing TRUE

# Controls the effort level of TNS optimization
set_optimization_strategy -tns_effort $ICC_TNS_EFFORT_POSTROUTE

if {[file exists [which $CUSTOM_ROUTE_OPT_PRE_SCRIPT]]} {
echo "RM-Info: Sourcing [which $CUSTOM_ROUTE_OPT_PRE_SCRIPT]"
source $CUSTOM_ROUTE_OPT_PRE_SCRIPT
}

########################################
#   TIO setup for route_opt command
########################################
if {$ICC_IMPLEMENTATION_PHASE == "top"} {
source -echo common_route_opt_tio_settings_icc.tcl
}

########################################
#   route_opt core command
########################################
## For running route_opt with filler cells placed :
#  The filler cells must be of type std_filler.
#  This is done by marking the std filler cells with gdsStdFillerCell during library dataprep.
#  If you see the following message when filler cells are inserted prior to route_opt,
#  then that means they are not marked properly :
#     WARNING : cell <xxx> is not of std filler cell subtype

## To enable verbose output for information related to route_opt operations, set the following.
#  See man page for complete details. Here's an example :
#    set_app_var routeopt_verbose 31

## To use the scenario compression feature, try the following :
#  open_mw_cel, etc 
#  compress_scenario
#  route_opt -skip_initial_route -effort $ROUTE_OPT_EFFORT -xtalk_reduction -power
#  route_opt -incremental ;# more run time benefit when multiple route_opt commands are used
#  uncompress_scenario
#  route_opt -incremental -size_only ;# to recover final QoR

set route_opt_cmd "route_opt -incremental -effort $ROUTE_OPT_EFFORT" 

if {!$IMPROVED_DESIGN_CLOSURE_FLOW} {
lappend route_opt_cmd -xtalk_reduction 
} elseif {$IMPROVED_DESIGN_CLOSURE_FLOW} {
lappend route_opt_cmd -area_recovery
}

if {!$IMPROVED_DESIGN_CLOSURE_FLOW} {
lappend route_opt_cmd -concurrent_clock_and_data 
}

## route_opt -power performs both power aware optimization (PAO, for ex, replacing LVT with HVT cells), 
#  and power recovery (PR, for ex, at the end of route_opt, recovering power by sizing).
#  If only PAO is desired and not PR, please do the following:
#  1. set_route_opt_strategy -power_aware_optimization true
#  2. comment out the line below (-power is not needed)
if {$POWER_OPTIMIZATION && !$IMPROVED_DESIGN_CLOSURE_FLOW} {lappend route_opt_cmd -power}

echo $route_opt_cmd
eval $route_opt_cmd

if {[file exists [which $CUSTOM_ROUTE_OPT_POST_SCRIPT]]} {
echo "RM-Info: Sourcing [which $CUSTOM_ROUTE_OPT_POST_SCRIPT]"
source $CUSTOM_ROUTE_OPT_POST_SCRIPT
}

if {$ICC_ENABLE_CHECKPOINT} {set_checkpoint_strategy -disable}

########################################
#   Additional route_opt practices
########################################
## For more on the post-H-2013.03 recommended postroute design closure flow, 
#  refer to SolvNet #038921
# Using the following flow can help further improvme QoR in postroute. 
# These steps come after the initial "route_opt -incremental":
if {$IMPROVED_DESIGN_CLOSURE_FLOW} {
set_app_var routeopt_enable_aggressive_optimization true
route_opt -incremental -xtalk_reduction -concurrent_clock_and_data
set_app_var routeopt_restrict_tns_to_size_only true
route_opt -incremental
}

## To limit route_opt to specific optimizations :
#  route_opt -incremental -only_xtalk_reduction : only xtalk reduction 
#  route_opt -incremental -only_hold_time : only hold fixing 
#  route_opt -incremental -(only_)wire_size : runs wire sizing which fixes timing by applying NDR's from define_routing_rule

## To prioritize max tran fixing :
#  By default, route_opt prioritizes max delay cost over max design rule costs (e.g. max tran). 
#  To set higher priority for DRC fixing, set the following variable.
#  Note that this variable only works with the -only_design_rule option.
#  set_app_var routeopt_drc_over_timing true
#    route_opt -incremental -only_design_rule

## To run size only but still allowing buffers to be inserted for hold fixing :
#  set_app_var routeopt_allow_min_buffer_with_size_only true
########################################

if { [check_error -verbose] != 0} { echo "RM-Error, flagging ..." }
########################################
#           CONNECT P/G                #
########################################
## Connect Power & Ground for non-MV and MV-mode

 if {[file exists [which $CUSTOM_CONNECT_PG_NETS_SCRIPT]]} {
   echo "RM-Info: Sourcing [which $CUSTOM_CONNECT_PG_NETS_SCRIPT]"
   source -echo $CUSTOM_CONNECT_PG_NETS_SCRIPT
 } else {
    derive_pg_connection -power_net $MW_POWER_NET -power_pin $MW_POWER_PORT -ground_net $MW_GROUND_NET -ground_pin $MW_GROUND_PORT 
    if {!$ICC_TIE_CELL_FLOW} {derive_pg_connection -power_net $MW_POWER_NET -ground_net $MW_GROUND_NET -tie}
   }
if { [check_error -verbose] != 0} { echo "RM-Error, flagging ..." }

save_mw_cel -as $ICC_ROUTE_OPT_CEL

# ELMOS
##Check for Ideal Nets
set num_ideal [sizeof_collection [all_ideal_nets]]
if {$num_ideal >= $ANA_NETS_NUM +1} {echo "Error: $num_ideal Nets are ideal after chip_finish_icc."}


if {$ICC_REPORTING_EFFORT == "MED" } {
 redirect -tee -file $REPORTS_DIR_ROUTE_OPT/$ICC_ROUTE_OPT_CEL.qor {report_qor}
 redirect -tee -file $REPORTS_DIR_ROUTE_OPT/$ICC_ROUTE_OPT_CEL.qor -append {report_qor -summary}
 # redirect -tee -file $REPORTS_DIR_PLACE_OPT/$ICC_ROUTE_OPT_CEL.qor -append {report_timing_histogram -range_maximum 0 -scenario [all_active_scenarios]}
 # redirect -tee -file $REPORTS_DIR_PLACE_OPT/$ICC_ROUTE_OPT_CEL.qor -append {report_timing_histogram -range_minimum 0 -scenario [all_active_scenarios]}
 redirect -file $REPORTS_DIR_ROUTE_OPT/$ICC_ROUTE_OPT_CEL.con {report_constraints}
}

if {$ICC_REPORTING_EFFORT != "OFF" } {
     if {[llength [get_scenarios -active true -setup true]]} {
     redirect -file $REPORTS_DIR_ROUTE_OPT/$ICC_ROUTE_OPT_CEL.clock_timing {report_clock_timing -nosplit -type skew -scenarios [get_scenarios -active true -setup true]} ;# local skew report
     redirect -tee -file $REPORTS_DIR_ROUTE_OPT/$ICC_ROUTE_OPT_CEL.max.clock_tree {report_clock_tree -nosplit -summary -scenarios [get_scenarios -active true -setup true]}     ;# global skew report
     }
     if {[llength [get_scenarios -active true -hold true]]} {
     redirect -tee -file $REPORTS_DIR_ROUTE_OPT/$ICC_ROUTE_OPT_CEL.min.clock_tree {report_clock_tree -nosplit -operating_condition min -summary -scenarios [get_scenarios -active true -hold true]}     ;# min global skew report
     }
}
if {$ICC_REPORTING_EFFORT != "OFF" } {
  redirect -file $REPORTS_DIR_ROUTE_OPT/$ICC_ROUTE_OPT_CEL.max.tim {report_timing -nosplit -crosstalk_delta -scenario [all_active_scenarios] -capacitance -transition_time -input_pins -nets -delay max}
  redirect -file $REPORTS_DIR_ROUTE_OPT/$ICC_ROUTE_OPT_CEL.min.tim {report_timing -nosplit -crosstalk_delta -scenario [all_active_scenarios] -capacitance -transition_time -input_pins -nets -delay min}
}
if {$ICC_REPORTING_EFFORT == "MED" && $POWER_OPTIMIZATION } {
  redirect -file $REPORTS_DIR_ROUTE_OPT/$ICC_ROUTE_OPT_CEL.power {report_power -nosplit -scenario [all_active_scenarios]}
}

## Uncomment if you want detailed routing violation report with or without antenna info
# ELMOS
if {$ICC_FIX_ANTENNA} {
   verify_zrt_route -antenna true ;
} else {
   verify_zrt_route -antenna false ;
  }



if {$ICC_REPORTING_EFFORT != "OFF" } {
 create_qor_snapshot -clock_tree -name $ICC_ROUTE_OPT_CEL
 redirect -file $REPORTS_DIR_ROUTE_OPT/$ICC_ROUTE_OPT_CEL.qor_snapshot.rpt {report_qor_snapshot -no_display}
}
## This script will check correlation between Primetime and StarRC and write out a timing and QoR report 
# For Primetime, if the variable values in ICC differ they will be changed to the PT value
if {[file exists [which $ICC_SIGNOFF_OPT_CHECK_CORRELATION_POSTROUTE_SCRIPT]]} { 
  source $ICC_SIGNOFF_OPT_CHECK_CORRELATION_POSTROUTE_SCRIPT 
}

puts "RM-Info: Completed script [info script]\n"

# ELMOS: removed, leave it to the main script if we want to exit the tool here
#exit

