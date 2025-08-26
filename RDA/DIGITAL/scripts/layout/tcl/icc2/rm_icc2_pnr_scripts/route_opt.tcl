##########################################################################################
# Script: route_opt.tcl
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

set REPORT_PREFIX $ROUTE_OPT_BLOCK_NAME
set REPORTS_DIR $REPORTS_DIR/$REPORT_PREFIX; file mkdir $REPORTS_DIR

open_lib $DESIGN_LIBRARY
copy_block -from ${DESIGN_NAME}/${ROUTE_AUTO_BLOCK_NAME} -to ${DESIGN_NAME}/${ROUTE_OPT_BLOCK_NAME}
current_block ${DESIGN_NAME}/${ROUTE_OPT_BLOCK_NAME}
link_block

## The following only applies to hierarchical designs
## Swap abstracts if abstracts specified for route_auto and route_opt are different
if {$DESIGN_STYLE == "hier"} {
	if {$USE_ABSTRACTS_FOR_BLOCKS != "" && ($BLOCK_ABSTRACT_FOR_ROUTE_OPT != $BLOCK_ABSTRACT_FOR_ROUTE_AUTO)} {
		puts "RM-info: Swapping from $BLOCK_ABSTRACT_FOR_ROUTE_AUTO to $BLOCK_ABSTRACT_FOR_ROUTE_OPT abstracts for all blocks."
		change_abstract -references $USE_ABSTRACTS_FOR_BLOCKS -label $BLOCK_ABSTRACT_FOR_ROUTE_OPT
		report_abstracts
	}
}

if {$ROUTE_OPT_ACTIVE_SCENARIO_LIST != ""} {
	set_scenario_status -active false [get_scenarios -filter active]
	set_scenario_status -active true $ROUTE_OPT_ACTIVE_SCENARIO_LIST
}


## Non-persistent settings to be applied in each step (optional)
rm_source -file $TCL_USER_NON_PERSISTENT_SCRIPT -optional -print "TCL_USER_NON_PERSISTENT_SCRIPT"

##########################################################################################
## Settings
##########################################################################################
## set_stage : a command to apply stage-based application options; intended to be used after set_qor_strategy within RM scripts.
set_stage -step post_route

## Prefix
set_app_options -name opt.common.user_instance_name_prefix -value route_opt_
set_app_options -name cts.common.user_instance_name_prefix -value route_opt_cts_


## For set_qor_strategy -metric leakage, disabling the dynamic power analysis in active scenarios for optimization
# Scenario power analysis will be renabled after optimization for reporting
if {$SET_QOR_STRATEGY_METRIC == "leakage_power"} {
   set rm_dynamic_scenarios [get_object_name [get_scenarios -filter active==true&&dynamic_power==true]]

   if {[llength $rm_dynamic_scenarios] > 0} {
      puts "RM-info: Disabling dynamic analysis for $rm_dynamic_scenarios"
      set_scenario_status -dynamic_power false [get_scenarios $rm_dynamic_scenarios]
  }
}

## StarRC in-design extraction (optional) : a config file is required to set up a proper StarRC run
## If a config file is not provided, route_opt reverts to ICC-II's native extraction. Example : route_opt.starrc_config_example.txt
if {[file exists [which $ROUTE_OPT_STARRC_CONFIG_FILE]]} {
	set_starrc_in_design -config $ROUTE_OPT_STARRC_CONFIG_FILE
} elseif {$ROUTE_OPT_STARRC_CONFIG_FILE != ""} {
	puts "RM-error: ROUTE_OPT_STARRC_CONFIG_FILE($ROUTE_OPT_STARRC_CONFIG_FILE) is invalid. Please correct it."
}

## StarRC in-design extraction validation flow
## Discover potential setup issues of StarRC in-design extraction before running route_opt.
## Low effort performs setup checks for config file path, StarRC path, layer mapping file path, and corner mapping;
## medium effort creates StarRC command file in your local dir; high effort invokes StarRC. 
#	check_starrc_in_design -effort <low|medium|high>


##########################################################################################
## Pre-route_opt customizations
##########################################################################################
rm_source -file $TCL_USER_ROUTE_OPT_PRE_SCRIPT -optional -print "TCL_USER_ROUTE_OPT_PRE_SCRIPT"

redirect -tee -file ${REPORTS_DIR}/${REPORT_PREFIX}.report_app_options.start {report_app_options -non_default *}
redirect -file ${REPORTS_DIR}/${REPORT_PREFIX}.report_lib_cell_purpose {report_lib_cell -objects [get_lib_cells] -column {full_name:20 valid_purposes}}

redirect -file ${REPORTS_DIR}/${REPORT_PREFIX}.report_qor.start {report_qor -scenarios [all_scenarios] -pba_mode [get_app_option_value -name time.pba_optimization_mode] -nosplit}
redirect -append -file ${REPORTS_DIR}/${REPORT_PREFIX}.report_qor.start {report_qor -summary -pba_mode [get_app_option_value -name time.pba_optimization_mode] -nosplit}
redirect -tee -file ${REPORTS_DIR}/${REPORT_PREFIX}.report_global_timing.start {report_global_timing -pba_mode [get_app_option_value -name time.pba_optimization_mode] -nosplit}

set check_stage_settings_cmd "check_stage_settings -stage pnr -metric \"${SET_QOR_STRATEGY_METRIC}\" -step post_route"
if {$ENABLE_REDUCED_EFFORT} {lappend check_stage_settings_cmd -reduced_effort}
if {$RESET_CHECK_STAGE_SETTINGS} {lappend check_stage_settings_cmd -reset_app_options}
redirect -file ${REPORTS_DIR}/${REPORT_PREFIX}.check_stage_settings {eval ${check_stage_settings_cmd}}


## The following only applies to designs with physical hierarchy
## Ignore the sub-blocks (bound to abstracts) internal timing paths
if {$DESIGN_STYLE == "hier" && $PHYSICAL_HIERARCHY_LEVEL != "bottom"} {
	set_timing_paths_disabled_blocks  -all_sub_blocks
}

##########################################################################################
## route_opt flow
##########################################################################################
compute_clock_latency

if {![rm_source -file $TCL_USER_ROUTE_OPT_SCRIPT -optional -print "TCL_USER_ROUTE_OPT_SCRIPT"]} {
## Note : the following executes if TCL_USER_ROUTE_OPT_SCRIPT is not sourced

	##########################################################################
	## First route_opt (CCD)
	##########################################################################
	## Without CLIB, route_opt issues TIM-260 and reverts to low accuracy delay model, even if search_path includes .db paths. 
	## Refer to message TIM-260 on how to enable library configuration to update reference libraries during open_lib.
	puts "RM-info: Running first route_opt (CCD)."
	route_opt
	#save_block -as ${DESIGN_NAME}/${ROUTE_OPT_BLOCK_NAME}_1

	rm_source -file $TCL_USER_ROUTE_OPT_1_POST_SCRIPT -optional -print "TCL_USER_ROUTE_OPT_1_POST_SCRIPT"

	##########################################################################
        ## IR Driven CCD (IRD-CCD)
        ##########################################################################
        ## Specify addtional IRDCCD confgurations as needed per your design. Enabled in the second route_opt.
        ## Example for IRD-CCD with RH : 	examples/TCL_IRDCCD_CONFIG_FILE.rh.tcl
        ## Example for IRD-CCD with RHSC : 	examples/TCL_IRDCCD_CONFIG_FILE.rhsc.tcl
	if {$ENABLE_IRDCCD} {
                rm_source -file $TCL_IRDCCD_CONFIG_FILE -print "IRD-CCD requires a proper TCL_IRDCCD_CONFIG_FILE"
	}

	##########################################################################
	## Second route_opt (non-CCD)
	##########################################################################
	## Turn off route_opt CCD for the second route_opt
	puts "RM-info: Setting route_opt.flow.enable_ccd to false for the second route_opt"
	set_app_options -name route_opt.flow.enable_ccd -value false ;# tool default false

	puts "RM-info: Running second route_opt (non-CCD)"
	route_opt

	## Disable IRDCCD before third route_opt if enabled at second route_opt
	if {$ENABLE_IRDCCD} {
		puts "RM-info: Disabling IDR-CCD by setting opt.common.power_integrity to false"
		set_app_options -name opt.common.power_integrity -value false
	}

	#save_block -as ${DESIGN_NAME}/${ROUTE_OPT_BLOCK_NAME}_2

	## Redundant via insertion
	if {$ENABLE_REDUNDANT_VIA_INSERTION} {
		add_redundant_vias -timing_preserve_setup_slack_threshold 0
	}

	rm_source -file $TCL_USER_ROUTE_OPT_2_POST_SCRIPT -optional -print "TCL_USER_ROUTE_OPT_2_POST_SCRIPT"

	##########################################################################
	## Third route_opt (non-CCD and size-only)
	##########################################################################
	if {!$ENABLE_ECO_OPT} {
	
		## Turn off route_opt CCD for the third route_opt
		puts "RM-info: Setting route_opt.flow.enable_ccd to false for the third route_opt"
		set_app_options -name route_opt.flow.enable_ccd -value false ;# tool default false
	
		## Reset power recovery to tool default for the third route_opt
		puts "RM-info: Resetting route_opt.flow.enable_clock_power_recovery for the third route_opt"
		reset_app_options route_opt.flow.enable_clock_power_recovery ;# tool default auto
	
		## Reset clock DRC fixing to tool default for the third route_opt
		puts "RM-info: Resetting route_opt.flow.enable_ccd_clock_drc_fixing for the third route_opt"
		reset_app_options route_opt.flow.enable_ccd_clock_drc_fixing ;# tool default auto
		
		## Size-only is recommended for the last route_opt in the flow
		## You can set the app option to a value appropriate to your library models, 
		## such as footprint, equal, or equal_or_smaller
		puts "RM-info: Setting route_opt.flow.size_only_mode to equal_or_smaller"   
		set_app_options -name route_opt.flow.size_only_mode -value equal_or_smaller
		
		puts "RM-info: Running third route_opt (non-CCD and size-only)"
		route_opt
	
	}

	##########################################################################
	## ECO fusion (replaces third route_opt)
	##########################################################################
	if {$ENABLE_ECO_OPT} {

		## Prerequisites : (1) PT path (2) license (3) ROUTE_OPT_ECO_OPT_STARRC_CONFIG_FILE
		## Note : (1) Best to use check_pt_qor with ECO fusion for timing/QoR reporting. 
		##            After ECO fusion is completed, any additional ICC-II report_* commands are based on ICC-II's native timer.
		##        (2) ECO Fusion doesn't support Fusion Extraction nor In-design StarRC.
		##	      If extract.starrc_mode = fusion_adv or in_design, ECO fusion runs with standalone StarRC extraction which requires 
		##	      a valid ROUTE_OPT_ECO_OPT_STARRC_CONFIG_FILE.
		if {$ROUTE_OPT_ECO_OPT_PT_PATH != "" && [check_license -quiet "Digital-AF"]} { 
			if {[get_app_option_value -name extract.starrc_mode] != "none"} {
				## ECO Fusion doesn't support fusion extraction and will still run standalone StarRC extraction
				if {[file exists [which $ROUTE_OPT_ECO_OPT_STARRC_CONFIG_FILE]]} {
					puts "RM-info: Running ECO fusion"
					rm_source -file route_opt.eco_opt.tcl
				} else {
					puts "RM-error: ROUTE_OPT_ECO_OPT_STARRC_CONFIG_FILE is invalid. ECO fusion is skipped"
				}
			} else {
				## ECO Fusion with ICC-II extraction
				puts "RM-info: Running ECO fusion with native extraction"
				rm_source -file route_opt.eco_opt.tcl
			}

		}
	
	}

}

##########################################################################################
## Target endpoint optimization	(optional)
##########################################################################################
## To optimize specific endpoints for setup, hold, or max_tran, specify the endpoints in a file 
## by using the -setup_endpoints, -hold_endpoints, or -max_transition options
## For ex, 
##	set_route_opt_target_endpoints -setup_endpoints $your_setup_endpoints_file
##
##	or 
#	## Collect endpoints through the get_timing_paths command (below is an example)
#	set target_endpoints [get_attribute [get_timing_paths -max_paths 1000 -from [all_registers -clock_pin] -to [all_registers -data_pin] \
#	-slack_lesser_than -0.002] endpoint]
#	set_route_opt_target_endpoints -setup_endpoints_collection $target_endpoints
##	route_opt

## To adjust the timing at specific endpoints for setup or hold (such as to adjust timing to achieve PT slack), 
## specify the endpoints and slack information in a file by using the -setup_timing or -hold_timing options
## For ex, 
##	set_route_opt_target_endpoints -setup_timing $your_setup_timing_file
##	report_qor -summary ;# generate report with adjusted timing before route_opt
##	route_opt
##	report_qor -summary ;# generate report with adjusted timing after route_opt
##	set_route_opt_target_endpoints -reset ;# remove adjusted timing
##	report_qor -summary ;# generate report without adjusted timing after route_opt

##########################################################################################
## PBA-CCD targeted optimization (optional)	
##########################################################################################
## Prerequisites : already done with RM's 3 route_opt flow : 1st CCD route_opt, 2nd route_opt with PBA enabled; 3rd size-only route_opt
## Run PBA-CCD skewing and datapath opto on selected end points for controlling optimization for last mile Fmax push
#	reset_app_options ccd.targeted_ccd* ;# disable app options intended for GBA in case they are set earlier in the flow
#	set_app_options -name route_opt.flow.enable_ccd -value true ;# tool default false; enables CCD 
#	set_app_options -name time.pba_optimization_mode -value path ;# for PBA
#	set_app_options -name route_opt.flow.enable_targeted_ccd_wns_optimization -value true ;# tool default false; enables targeted CCD
#
#	## Collect endpoints through the get_timing_paths command (below is an example)
#	set target_endpoints [get_attribute [get_timing_paths -max_paths 1000 -from [all_registers -clock_pin] -to [all_registers -data_pin] \
#	-slack_lesser_than -0.002] endpoint]
#	set_route_opt_target_endpoints -setup_endpoints_collection $target_endpoints
#	route_opt

## Redundant via insertion, command execution
## For designs with advanced nodes where DRC convergence could be a concern, it is recommended to be done after route_auto/route_opt
if {$ENABLE_REDUNDANT_VIA_INSERTION} {
	add_redundant_vias
}

## Fix remaining routing DRCs
#route_detail -incremental true -initial_drc_from_input true

## Create shields
if {$ENABLE_CREATE_SHIELDS} {
	if {$CREATE_SHIELDS_GROUND_NET != ""} {
		create_shields -shielding_mode reshield -with_ground $CREATE_SHIELDS_GROUND_NET
	} else {
		create_shields -shielding_mode reshield
	}
}

##########################################################################################
## Post-route_opt customizations
##########################################################################################
rm_source -file $TCL_USER_ROUTE_OPT_POST_SCRIPT -optional -print "TCL_USER_ROUTE_OPT_POST_SCRIPT" 

##########################################################################################
## connect_pg_net
##########################################################################################
if {![rm_source -file $TCL_USER_CONNECT_PG_NET_SCRIPT -optional -print "TCL_USER_CONNECT_PG_NET_SCRIPT"]} {
## Note : the following executes if TCL_USER_CONNECT_PG_NET_SCRIPT is not sourced
	connect_pg_net
        # For non-MV designs with more than one PG, you should use connect_pg_net in manual mode.
}

## Run check_routes to save updated routing DRC to the block
redirect -tee -file ${REPORTS_DIR}/${REPORT_PREFIX}.check_routes {check_routes}

## Re-enable power analysis if disabled for set_qor_strategy -metric timing
if {[info exists rm_dynamic_scenarios] && [llength $rm_dynamic_scenarios] > 0} {
   puts "RM-info: Reenabling dynamic power analysis for $rm_dynamic_scenarios"
   set_scenario_status -dynamic_power true [get_scenarios $rm_dynamic_scenarios]
}

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
                derive_hier_antenna_property -design ${DESIGN_NAME}/${ROUTE_OPT_BLOCK_NAME}
                save_block ${DESIGN_NAME}/${ROUTE_OPT_BLOCK_NAME}.frame
	} elseif { $PHYSICAL_HIERARCHY_LEVEL == "intermediate"} {
		if { $ABSTRACT_TYPE_FOR_MPH_BLOCKS == "nested"} {
			## Create nested abstract for the intermediate level of physical hierarchy
			create_abstract -read_only
		} elseif { $ABSTRACT_TYPE_FOR_MPH_BLOCKS == "flattened"} {
			## Create flattened abstract for the intermediate level of physical hierarchy
			create_abstract -read_only -preserve_block_instances false
		}
                create_frame -block_all true
                derive_hier_antenna_property -design ${DESIGN_NAME}/${ROUTE_OPT_BLOCK_NAME}
		save_block ${DESIGN_NAME}/${ROUTE_OPT_BLOCK_NAME}.frame
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
#echo [date] > route_opt

# ELMOS: removed, leave it to main script to decide if we exit here
#exit 
