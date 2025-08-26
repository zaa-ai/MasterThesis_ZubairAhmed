##########################################################################################
# Script: clock_opt_cts.tcl
# Version: S-2021.06
# Copyright (C) 2014-2021 Synopsys, Inc. All rights reserved.
##########################################################################################

# ELMOS: appended scripts path
source $env(PROJECT_HOME)/scripts/layout/tcl/icc2/rm_utilities/procs_global.tcl 
source $env(PROJECT_HOME)/scripts/layout/tcl/icc2/rm_utilities/procs_icc2.tcl 
# ELMOS: sourced from project specific control file
#rm_source -file ./rm_setup/design_setup.tcl
#rm_source -file ./rm_setup/icc2_pnr_setup.tcl
#rm_source -file ./rm_setup/header_icc2_pnr.tcl

set REPORT_PREFIX $CLOCK_OPT_CTS_BLOCK_NAME
set REPORTS_DIR $REPORTS_DIR/$REPORT_PREFIX; file mkdir $REPORTS_DIR

open_lib $DESIGN_LIBRARY
copy_block -from ${DESIGN_NAME}/${PLACE_OPT_BLOCK_NAME} -to ${DESIGN_NAME}/${CLOCK_OPT_CTS_BLOCK_NAME}
current_block ${DESIGN_NAME}/${CLOCK_OPT_CTS_BLOCK_NAME}
link_block

## The following only applies to hierarchical designs
## Swap abstracts if abstracts specified for place_opt and clock_opt_cts are different
if {$DESIGN_STYLE == "hier"} {
	if {$USE_ABSTRACTS_FOR_BLOCKS != "" && ($BLOCK_ABSTRACT_FOR_CLOCK_OPT_CTS != $BLOCK_ABSTRACT_FOR_PLACE_OPT)} {
		puts "RM-info: Swapping from $BLOCK_ABSTRACT_FOR_PLACE_OPT to $BLOCK_ABSTRACT_FOR_CLOCK_OPT_CTS abstracts for all blocks."
		change_abstract -references $USE_ABSTRACTS_FOR_BLOCKS -label $BLOCK_ABSTRACT_FOR_CLOCK_OPT_CTS
		report_abstracts
	}
}

## Set active scenarios for the step (please include CTS and hold scenarios for CCD)
if {$CLOCK_OPT_CTS_ACTIVE_SCENARIO_LIST != ""} {
	set_scenario_status -active false [get_scenarios -filter active]
	set_scenario_status -active true $CLOCK_OPT_CTS_ACTIVE_SCENARIO_LIST
}

if {[sizeof_collection [get_scenarios -filter "hold && active"]] == 0} {
	puts "RM-warning: No active hold scenario is found. Recommended to enable hold scenarios here such that CCD skewing can consider them." 
	puts "RM-info: Please activate hold scenarios for CTS if they are available." 
}



## Non-persistent settings to be applied in each step (optional)
rm_source -file $TCL_USER_NON_PERSISTENT_SCRIPT -optional -print "TCL_USER_NON_PERSISTENT_SCRIPT"

##########################################################################################
## Settings
##########################################################################################
## set_stage : a command to apply stage-based application options; intended to be used after set_qor_strategy within RM scripts.
set_stage -step cts

## Prefix
set_app_options -name cts.common.user_instance_name_prefix -value clock_opt_cts_
set_app_options -name opt.common.user_instance_name_prefix -value clock_opt_cts_opt_

## For set_qor_strategy -metric timing, disabling the leakage and dynamic power analysis in active scenarios for optimization
## For set_qor_strategy -metric leakage, disabling the dynamic power analysis in active scenarios for optimization
# Scenario power analysis will be renabled after optimization for reporting
if {$SET_QOR_STRATEGY_METRIC == "timing"} {
   set rm_leakage_scenarios [get_object_name [get_scenarios -filter active==true&&leakage_power==true]]
   set rm_dynamic_scenarios [get_object_name [get_scenarios -filter active==true&&dynamic_power==true]]

   if {[llength $rm_leakage_scenarios] > 0 || [llength $rm_dynamic_scenarios] > 0} {
      puts "RM-info: Disabling leakage analysis for $rm_leakage_scenarios"
      puts "RM-info: Disabling dynamic analysis for $rm_dynamic_scenarios"
      set_scenario_status -leakage_power false -dynamic_power false [get_scenarios "$rm_leakage_scenarios $rm_dynamic_scenarios"]
   }
} elseif {$SET_QOR_STRATEGY_METRIC == "leakage_power"} {
   set rm_dynamic_scenarios [get_object_name [get_scenarios -filter active==true&&dynamic_power==true]]

   if {[llength $rm_dynamic_scenarios] > 0} {
      puts "RM-info: Disabling dynamic analysis for $rm_dynamic_scenarios"
      set_scenario_status -dynamic_power false [get_scenarios $rm_dynamic_scenarios]
  }
}

## Antenna fixing is on by default since route.detail.antenna is default true
rm_source -file $TCL_ANTENNA_RULE_FILE -optional -print "TCL_ANTENNA_RULE_FILE"

##########################################################################################
## Pre-CTS customizations
##########################################################################################
rm_source -file $TCL_USER_CLOCK_OPT_CTS_PRE_SCRIPT -optional -print "TCL_USER_CLOCK_OPT_CTS_PRE_SCRIPT"

redirect -tee -file ${REPORTS_DIR}/${REPORT_PREFIX}.report_app_options.start {report_app_options -non_default *}
redirect -file ${REPORTS_DIR}/${REPORT_PREFIX}.report_lib_cell_purpose {report_lib_cell -objects [get_lib_cells] -column {full_name:20 valid_purposes}}
redirect -file ${REPORTS_DIR}/${REPORT_PREFIX}.pre_cts.report_clock_settings {report_clock_settings} ;# CTS constraints and settings
redirect -file ${REPORTS_DIR}/${REPORT_PREFIX}.pre_cts.check_clock_tree {check_clock_tree} ;# checks issues that could hurt CTS results

redirect -file ${REPORTS_DIR}/${REPORT_PREFIX}.report_qor.start {report_qor -scenarios [all_scenarios] -pba_mode [get_app_option_value -name time.pba_optimization_mode] -nosplit}
redirect -append -file ${REPORTS_DIR}/${REPORT_PREFIX}.report_qor.start {report_qor -summary -pba_mode [get_app_option_value -name time.pba_optimization_mode] -nosplit}
redirect -tee -file ${REPORTS_DIR}/${REPORT_PREFIX}.report_global_timing.start {report_global_timing -pba_mode [get_app_option_value -name time.pba_optimization_mode] -nosplit}

set check_stage_settings_cmd "check_stage_settings -stage pnr -metric \"${SET_QOR_STRATEGY_METRIC}\" -step cts"
if {$ENABLE_REDUCED_EFFORT} {lappend check_stage_settings_cmd -reduced_effort}
if {$RESET_CHECK_STAGE_SETTINGS} {lappend check_stage_settings_cmd -reset_app_options}
redirect -file ${REPORTS_DIR}/${REPORT_PREFIX}.check_stage_settings {eval ${check_stage_settings_cmd}}


## Enabled if used by top level closure flow
if {$DESIGN_STYLE == "hier"} { 
	## Promote clock tree exceptions from blocks to top
	if {$USE_ABSTRACTS_FOR_BLOCKS != "" && $PROMOTE_CLOCK_BALANCE_POINTS} {
		promote_clock_data -auto_clock connected -balance_points
	}
}

## Uncomment the following lines when using CCD-done blocks
#  The following command promotes the median latency information from the blocks (stored during compute_clock_latency at block-level) as balance points on the clock pins
#  set_block_to_top_map -auto_clock connected -report_only ; # resolve any warnings/ errors reported by this command
#  promote_clock_data -port_latency -auto_clock connected

## The following only applies to designs with physical hierarchy
## Ignore the sub-blocks (bound to abstracts) internal timing paths
if {$DESIGN_STYLE == "hier" && $PHYSICAL_HIERARCHY_LEVEL != "bottom"} {
	set_timing_paths_disabled_blocks  -all_sub_blocks
}

##########################################################################################
## Multisource clock tree synthesis (MSCTS)
##########################################################################################
if {[file exists [which $TCL_USER_MSCTS_MESH_ROUTING_SCRIPT]]} {
	#Remove dont_touch 
	mark_clock_trees -clear -dont_touch
	rm_source -file $TCL_USER_MSCTS_MESH_ROUTING_SCRIPT -optional -print "TCL_USER_MSCTS_MESH_ROUTING_SCRIPT"
} 	

##########################################################################################
## clock_opt CTS flow
##########################################################################################
## Reminder: Include flops as part of the cts lib cell purpose list :
## CCD can size flops to improve timing. Please make sure flops are enabled for CTS to allow sizing during CCD.

# Registers are marked application_fixed before CTS to preserve location 
set clock_sinks [all_fanout -clock_tree -end -flat -only_cell]
set clock_filt [filter_collection $clock_sinks "is_sequential && !is_integrated_clock_gating_cell && !is_mux && physical_status != fixed"]
set_placement_status application_fixed $clock_filt

if {![rm_source -file $TCL_USER_CLOCK_OPT_CTS_SCRIPT -optional -print "TCL_USER_CLOCK_OPT_CTS_SCRIPT"]} {
# Note : The following executes if TCL_USER_CLOCK_OPT_CTS_SCRIPT is not sourced

	puts "RM-info: Running check for relaxed clock transition constraint" 	
	check_clock_transition -threshold 0.15 -apply_max_transition

	puts "RM-info: Running clock_opt -from build_clock -to build_clock command"
	clock_opt -from build_clock -to build_clock
	#save_block -as ${DESIGN_NAME}/clock_opt_build_clock

	#If relaxed clock transition applied, original constraint will be restored
	restore_clock_transition	
	
	puts "RM-info: Running clock_opt -from route_clock -to route_clock command"
	clock_opt -from route_clock -to route_clock

}

## Redundant via insertion
if {$ENABLE_REDUNDANT_VIA_INSERTION} {
	## Source ICC-II via mapping file for redundant via insertion
        # ELMOS: commented out, seems not to be necessary (at least in TSMC 180nm and Samsung 130 nm
	#rm_source -file $TCL_USER_REDUNDANT_VIA_MAPPING_FILE -print "ENABLE_REDUNDANT_VIA_INSERTION is TRUE but TCL_USER_REDUNDANT_VIA_MAPPING_FILE is not valid"
	report_via_mapping

	add_redundant_vias
}

## Enable AOCV (recommended after CTS is completed)
if {$AOCV_CORNER_TABLE_MAPPING_LIST != "" && ![get_app_option_value -name time.pocvm_enable_analysis]} {
	## Enable the AOCV analysis
	set_app_options -name time.aocvm_enable_analysis -value true ;# default false

	## Enable the AOCV distance analysis (optional)
	## AOCV analysis will consider path distance when calculating AOCVM derate
	#	set_app_options -name time.ocvm_enable_distance_analysis -value true ;# default false
	
	## Set the configuration for the AOCV analysis (optional)
	#	set_app_options -name time.aocvm_analysis_mode -value separate_launch_capture_depth ;# default separate_launch_capture_depth
}

##########################################################################################
## Post-CTS customizations
##########################################################################################
rm_source -file $TCL_USER_CLOCK_OPT_CTS_POST_SCRIPT -optional -print "TCL_USER_CLOCK_OPT_CTS_POST_SCRIPT"

##########################################################################################
## Propagate all clocks 
##########################################################################################
## This should be used only when additional modes/scenarios are activated after CTS is done.
## Get inactive scenarios, activate them, mark them as propagated, and then deactivate them.
#	if {[sizeof_collection [get_scenarios -filter active==false -quiet]] > 0} {
#	        set active_scenarios [get_scenarios -filter active]
#	        set inactive_scenarios [get_scenarios -filter active==false]
#
#	        set_scenario_status -active false [get_scenarios $active_scenarios]
#	        set_scenario_status -active true [get_scenarios $inactive_scenarios]
#
#	        synthesize_clock_trees -propagate_only ;# only works on active scenarios
#	        set_scenario_status -active true [get_scenarios $active_scenarios]
#	        set_scenario_status -active false [get_scenarios $inactive_scenarios]
#	}

##########################################################################################
## connect_pg_net
##########################################################################################
if {![rm_source -file $TCL_USER_CONNECT_PG_NET_SCRIPT -optional -print "TCL_USER_CONNECT_PG_NET_SCRIPT"]} {
## Note : the following executes if TCL_USER_CONNECT_PG_NET_SCRIPT is not sourced
	connect_pg_net
        # For non-MV designs with more than one PG, you should use connect_pg_net in manual mode.
}

## Re-enable power analysis if disabled for set_qor_strategy -metric timing
if {[info exists rm_leakage_scenarios] && [llength $rm_leakage_scenarios] > 0} {
   puts "RM-info: Reenabling leakage power analysis for $rm_leakage_scenarios"
   set_scenario_status -leakage_power true [get_scenarios $rm_leakage_scenarios]
}
if {[info exists rm_dynamic_scenarios] && [llength $rm_dynamic_scenarios] > 0} {
   puts "RM-info: Reenabling dynamic power analysis for $rm_dynamic_scenarios"
   set_scenario_status -dynamic_power true [get_scenarios $rm_dynamic_scenarios]
}

## Run check_routes to save updated routing DRC to the block
redirect -tee -file ${REPORTS_DIR}/${REPORT_PREFIX}.check_routes {check_routes -open_net false}

## Save block
save_block

##########################################################################################
## Create abstract and frame
##########################################################################################
## Enabled for hierarchical designs; for bottom and intermediate levels of physical hierarchy
if {$DESIGN_STYLE == "hier"} {
        if {$USE_ABSTRACTS_FOR_POWER_ANALYSIS == "true"} {
                set_app_options -name abstract.annotate_power -value true
        }
        if { $PHYSICAL_HIERARCHY_LEVEL == "bottom" } {
                create_abstract -read_only
                create_frame -block_all true
        } elseif { $PHYSICAL_HIERARCHY_LEVEL == "intermediate"} {
            if { $ABSTRACT_TYPE_FOR_MPH_BLOCKS == "nested"} {
                ## Create nested abstract for the intermediate level of physical hierarchy
                create_abstract -read_only
                create_frame -block_all true
            } elseif { $ABSTRACT_TYPE_FOR_MPH_BLOCKS == "flattened"} {
                ## Create flattened abstract for the intermediate level of physical hierarchy
                create_abstract -read_only -preserve_block_instances false
                create_frame -block_all true
            }
        }
}

##########################################################################################
## Report and output
##########################################################################################
if {$REPORT_QOR} {
	if {$REPORT_PARALLEL_SUBMIT_COMMAND != ""} {
		## Generate a file to pass necessary RM variables for running report_qor.tcl to the report_parallel command
		rm_generate_variables_for_report_parallel -work_directory ${REPORTS_DIR} -file_name rm_tcl_var.tcl

		## Parallel reporting using the report_parallel command (requires a valid REPORT_PARALLEL_SUBMIT_COMMAND)
		report_parallel -work_directory ${REPORTS_DIR} -submit_command ${REPORT_PARALLEL_SUBMIT_COMMAND} -max_cores ${REPORT_PARALLEL_MAX_CORES} -user_scripts [list "${REPORTS_DIR}/rm_tcl_var.tcl" "[which report_qor.tcl]"]
	} else {
		## Classic reporting
		rm_source -file report_qor.tcl
	}
}

print_message_info -ids * -summary
# ELMOS: removed, as this breaks the checker script functionality
#echo [date] > clock_opt_cts

# ELMOS: removed, leave it to main script to decide if we exit here
#exit 
