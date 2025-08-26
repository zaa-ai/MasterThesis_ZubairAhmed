if {[file exists user_tcl/icc_setup.tcl]} {
  source -echo user_tcl/icc_setup.tcl
  return
}

#######################################################################################
### This scripts is not sourced, if an user_Tcl/icc_setup.tcl exists
#######################################################################################

puts "RM-Info: Running script [info script]\n"

##########################################################################################
# Variables for IC Compiler Reference Methodology, IC Compiler Design Planning Reference
# Methodology, and IC Compiler Hierarchical Reference Methodology
# Script: icc_setup.tcl
# Version: M-2016.12-SP4 (July 17, 2017)
# Copyright (C) 2010-2017 Synopsys, Inc. All rights reserved.
##########################################################################################

# Sourcing the common variables
# source -echo ./rm_setup/common_setup.tcl

# ELMOS: specify target value for ideal nets
set ANA_NETS_NUM 0

###############################
## Flow Variables
###############################
# ELMOS: use DDC flow
set ICC_INIT_DESIGN_INPUT         "DDC"        ;# VERILOG|DDC|MW; specify the type of starting point;
                                       ;# if "VERILOG" is specified, you should also specify a valid $ICC_IN_VERILOG_NETLIST_FILE
                                       ;# if "DDC" is specified, you should also specify a valid $ICC_IN_DDC_FILE 
                                       ;# if "MW" is specified, you should also specify a valid $ICC_INPUT_CEL
# ELMOS: disabled
set POWER_OPTIMIZATION            FALSE        ;# TRUE|FALSE; set TRUE to enable power optimization (-power option) for the core commands such as place_opt, clock_opt, 
                                       ;# route_opt, and focal_opt. If $ICC_CUSTOM_MULTI_VTH_CONSTRAINT_SCRIPT below is also specified, 
                                       ;# leakage power optimization is focused on lvt cell reduction; otherwise focused on leakage power reduction.
                                       ;# for MCMM, set set_scenario_options -leakage true to enable leakage power optimization on scenarios;
                                       ;# see rm_icc_scripts/mcmm.scenarios.example for more details.
set ICC_PLACE_LOW_POWER_PLACEMENT FALSE        ;# TRUE|FALSE; set TRUE to enable low power placement for place_opt; requires $POWER_OPTIMIZATION to be TRUE to be effective.

                                       ;# for MCMM, this feature requires you to set set_scenario_options -dynamic true;
                                       ;# see rm_icc_scripts/mcmm.scenarios.example for more details.
set ICC_CUSTOM_MULTI_VTH_CONSTRAINT_SCRIPT ""  ;# script for customized set_multi_vth_constraints constraints. effective only when $POWER_OPTIMIZATION is set to TRUE;
                                       ;# specify to make leakage power optimization focused on lvt cell reduction; 
                                       ;# refer to rm_icc_scripts/multi_vth_constraint.example as an example.      
# ELMOS: scan-reordering by default
set DFT                           TRUE         ;# TRUE|FALSE; set TRUE to enable scan reordering flow and add -optimize_dft option to place_opt and clock_opt commands;
;# if set TRUE, you should also provide a valid $ICC_IN_SCAN_DEF_FILE
# ELMOS: use TIE cells
set ICC_TIE_CELL_FLOW             TRUE         ;# TRUE|FALSE, set TRUE if you want TIE-CELLS to be used during optimizations instead of TIE-nets
set ICC_DBL_VIA                   TRUE         ;# TRUE|FALSE; set TRUE to enable redundant via insertion; more options in "Chipfinishing and Metal Fill Variables" section
# ELMOS: fix antennas
set ICC_FIX_ANTENNA               TRUE         ;# TRUE|FALSE: set TRUE to enable antenna fixing; more options in "Chipfinishing Variables" section
# ELMOS: filler cells
set ADD_FILLER_CELL               TRUE         ;# TRUE|FALSE; set TRUE to enable std cells filler insertion; more options in "Chipfinishing Variables" section
set ICC_CREATE_MODEL              FALSE        ;# TRUE|FALSE; set TRUE to create block abstraction and FRAM view (at block level)
set ICC_REDUCE_CRITICAL_AREA      TRUE         ;# TRUE|FALSE; set TRUE to enable detail route wire spreading
set ADD_METAL_FILL                "ICC"        
                                       ;# Note : It is recommended to use ICV with signoff_metal_fill command for technology nodes 45nm and below
                                               
                                               ;# ICV : signoff_metal_fill using IC Validator
set ICC_REPORTING_EFFORT          "MED"        ;# OFF|LOW|MED; if set to OFF, no reporting is done; if set to LOW, report_qor/report_constraints/report_power are skipped,
                                       ;# additionally, report_timing is skipped in clock_opt_cts
set ICC_SANITY_CHECK              FALSE        ;# TRUE|FALSE, set TRUE to perform check_physical_design
set ICC_ENABLE_CHECKPOINT    FALSE             ;# TRUE|FALSE, set TRUE to perform checkpoint strategy for optimization commands 
                                       ;# ensure there is enough disk space before enabling this feature. refer to the set_checkpoint_strategy man page for details.

set IMPROVED_DESIGN_CLOSURE_FLOW        FALSE   ;# FALSE|TRUE; set to TRUE to enable the postroute design closure flow after initial routing. 
                                                ;# This will run two additional route_opt -incremental commands in route_opt_icc.tcl

###############################
## General Variables
###############################
set ICC_INPUT_CEL                 "${DESIGN_NAME}_DCT" ;# starting CEL for flow with a Milkyway CEL input which can be the final CEL from Design Compiler Topographical
set PNET_METAL_LIST               ""             ;# List of metals in the design to be used for (partial) pnet options
set PNET_METAL_LIST_COMPLETE      ""             ;# List of metals in the design to be used for (complete) pnet options
set ICC_IN_DONT_USE_FILE          "$LIBRARY_DONT_USE_FILE" ;# script with library modifications for dont_use; default to $LIBRARY_DONT_USE_FILE in common_setup.tcl
set ICC_FIX_HOLD_PREFER_CELLS     ""             ;# Syntax: library/cell_name - Example: slow/DLY1X1 slow/DLY1X4
set ICC_MAX_AREA                  ""             ;# max_area value used during area optimization
set MW_EXTENDED_LAYER_MODE        FALSE          ;# FALSE|TRUE: Default FALSE creates a Milkyway design library with the default layer mode that supports user defined and routing layers on layers 1-187 in the technology file. Setting this to TRUE will create a library in the extended layer mode that supports from layers 1-4000 in the technology file.
set AREA_CRITICAL_RANGE_PRE_CTS   ""             ;# area critical range use during area optimization during place_opt
set AREA_CRITICAL_RANGE_POST_CTS  ""             ;# area critical range use during area optimization during post-CTS optimization
set AREA_CRITICAL_RANGE_POST_RT   ""             ;# area critical range use during area optimization during route_opt
set POWER_CRITICAL_RANGE_PRE_CTS  ""             ;# power critical range use during area optimization during place_opt
set POWER_CRITICAL_RANGE_POST_CTS ""             ;# power critical range use during area optimization during post-CTS optimization
set POWER_CRITICAL_RANGE_POST_RT  ""             ;# power critical range use during area optimization during route_opt
set ICC_NUM_CPUS                  1              ;# number of cpus for distributed processing
                                                 ;# specify a number greater than 1 to enable it for classic router based route_opt and insert_redundant_via commands
set ICC_NUM_CORES                 8              ;# number of cores on the local host for multicore support; 
                                                 ;# specify a number greater than 1 to enable it for the core commands
set PLACE_OPT_EFFORT             "medium"        ;# low|medium|high; choose effort level for place_opt command
set PLACE_OPT_TRADEOFF_TIMING_FOR_POWER_AREA FALSE ;# TRUE|FALSE; set TRUE to enable timing, power and area tradeoff optimization for place_opt command.
                                                 ;# It works for medium or high effort place_opt with -power option
set ROUTE_OPT_EFFORT             "high"          ;# low|medium|high; choose effort level for route_opt command
set PLACE_OPT_CONGESTION_DRIVEN  "TRUE"          ;# TRUE|FALSE; set TRUE to enable congestion removal during place_opt command (place_opt_icc step) and 
                                                 ;# clock_opt -only_psyn command (clock_opt_psyn_icc step) 
set ICC_PLACE_OPTIMIZE_ICGS      "TRUE"          ;# TRUE|FALSE: Set to TRUE to use the -optimize_icgs option in the CCD flow for place_opt and create_placement.  
set ICC_CLOCK_OPT_CCD_EFFORT     "HIGH"          ;# HIGH|MEDIUM: Set to HIGH by default.  Controls the CCD effort in clock_opt.MEDIUM effort flow will perform the first two clock_opt commands with CCD for CTS and optimization. HIGH effort flow will perform a third clock_opt for incremental CCD improvements.  
                                                 ;# The MEDIUM effort CCD flow can reduce runtime but QoR at the end of clock_opt may look worse compared to the HIGH effort CCD flow. However we expect the QoR after post-route-optimization to be close to the HIGH effort CCD flow.

set PLACE_OPT_LAYER_OPTIMIZATION  "TRUE" ;# TRUE|FALSE: Set to TRUE by default to control whether layer optimization is performed during place_opt by set_place_opt_strategy -layer_optimization

# ELMOS: medium -> high
set PLACE_OPT_LAYER_OPTIMIZATION_EFFORT  "HIGH" ;# medium|high: Set to medium by default. Controls the layer optimization effort during place_opt

set PLACE_OPT_CONSIDER_ROUTING          "FALSE" ;# FALSE|TRUE: Default FALSE. Controls whether track RC based optimization is performed during place_opt
                                        ;# The RC models are generated from the current scenario so set the most critical scenario as the current scenario before running place_opt
set ICC_TOTAL_POWER_STRATEGY_EFFORT  none       ;# none|medium|high; set to medium or high to improve total power (leakage + dynamic)
                                        ;# A realistic SAIF will be needed to get accurate power savings
                                                ;# For MCMM design an active scenario with dynamic_power, leakage_power, and setup enabled is necessary for total power optimization
                                        ;# Applies to place_opt -power, psynopt -power, and psynopt -only_power

set ICC_HIGH_RESISTANCE_OPTIMIZATION  "FALSE" ;# FALSE|TRUE: Default FALSE. Setting to TRUE will enable the high resistance optimization for route_opt and focal_opt. This feature may see increased effect on 20nm and below designs.

# ELMOS: medium -> high
set ICC_TNS_EFFORT_PREROUTE     "HIGH" ;# MEDIUM|HIGH: Default MEDIUM. Controls the effort of preroute optimization to explore TNS improvements. When set to HIGH preroute optimzation will spend longer looking for TNS improvements. Affects place_opt, clock_opt -only_psyn, psynopt, and preroute_focal_opt.

# ELMOS: medium -> high
set ICC_TNS_EFFORT_POSTROUTE    "HIGH"   ;# MEDIUM|HIGH: Default MEDIUM. Controls the effort of postroute optimization to explore TNS improvements. When set to HIGH postroute optimzation will spend longer looking for TNS improvements. Affects route_opt and focal_opt.

set PLACE_OPT_PREROUTE_FOCALOPT_LAYER_OPTIMIZATION FALSE 
                                        ;# TRUE|FALSE; set TRUE to perform layer optimization (preroute_focal_opt -layer_optimization) 
                                        ;# on existing buffer trees after place_opt command (place_opt_icc step)
set CLOCK_OPT_PSYN_PREROUTE_FOCALOPT_LAYER_OPTIMIZATION FALSE 
                                        ;# TRUE|FALSE; set TRUE to perform layer optimization (preroute_focal_opt -layer_optimization) 
                                        ;# on existing buffer trees after clock_opt -only_psyn command (clock_opt_psyn_icc step)
set CLOCK_OPT_PSYN_PREROUTE_FOCALOPT_AUTO_NDR FALSE
                                        ;# TRUE|FALSE; set TRUE will perform optimization with automatic routing rules (preroute_focal_opt -auto_routing_rule) 
                                        ;# on existing buffer trees after clock_opt -only_psyn command (clock_opt_psyn_icc step)
set ICC_CREATE_GR_PNG             FALSE       ;# TRUE|FALSE; set TRUE to create a global route congestion map snapshot in PNG format at the end of route_icc step
set ICC_WRITE_FULL_CHIP_VERILOG   FALSE         ;# TRUE|FALSE; set TRUE for write_verilog in outputs_icc.tcl to write out module definitions for soft macros

# ELMOS: get rules from TECHXML
if {![info exists MW_POWER_NET]} {
    set MW_POWER_NET                  [exec getPrjCfg.rb -r $TECH tech/phys/pwr]
}
if {![info exists MW_POWER_PORT]} {
    set MW_POWER_PORT                 [exec getPrjCfg.rb -r $TECH tech/phys/pwr]
}
if {![info exists MW_GROUND_NET]} {
    set MW_GROUND_NET                 [exec getPrjCfg.rb -r $TECH tech/phys/gnd]
}
if {![info exists MW_GROUND_PORT]} {
    set MW_GROUND_PORT                [exec getPrjCfg.rb -r $TECH tech/phys/gnd]
}
if {![info exists MW_SUB_NET]} {
    set MW_SUB_NET            	  [exec getPrjCfg.rb -r $TECH tech/phys/subnet]
}
#############################
## Cellname Variables
###############################
set ICC_FLOORPLAN_CEL            "init_design_icc"
set ICC_PLACE_OPT_CEL            "place_opt_icc"
set ICC_CLOCK_OPT_CCD_CEL        "clock_opt_ccd_icc"
set ICC_CLOCK_OPT_ROUTE_CEL      "clock_opt_route_icc"
set ICC_ROUTE_CEL                "route_icc"
set ICC_ROUTE_OPT_CEL            "route_opt_icc"
set ICC_CHIP_FINISH_CEL          "chip_finish_icc"
set ICC_METAL_FILL_CEL           "metal_fill_icc"

set ICC_ECO_STARTING_CEL   	 $ICC_METAL_FILL_CEL         ;# CEL to run ECO on (contains original pre-tape-out database)
set ICC_ECO_CEL                  "eco_icc"                   ;# CEL after running the ECO (contains new ECO netlist)
set ICC_FOCAL_OPT_STARTING_CEL   $ICC_CHIP_FINISH_CEL        ;# CEL to run focal_opt on
set ICC_FOCAL_OPT_CEL            "focal_opt_icc"             ;# CEL after running focal_opt
set ICC_OUTPUTS_CEL     	 "outputs_icc"                ;# CEL after change_names for output
set ICC_FLOORPLAN_ODL_CEL   	 "init_design_odl"
set ICC_DP_CREATE_PLANGROUPS_CEL "create_plangroups_dp"
set ICC_DP_CREATE_ODL_CEL   	 "create_odl_dp"
set ICC_DP_ROUTEABILITY_ON_PLANGROUPS_CEL "routeability_on_plangroups_dp"
set ICC_DP_PIN_ASSIGNMENT_BUDGETING_CEL   "pin_assignment_budgeting_dp"
set ICC_DP_COMMIT_CEL    	 "commit_dp"

############################################################
## Customized Constraint Script for Core Commands (Optional)
############################################################
set CUSTOM_INIT_DESIGN_PRE_SCRIPT ""    ;# An optional Tcl file; if specified, will be sourced before the read_def command;
                                        ;# review init_design_icc.tcl script for exact location where this is sourced to avoid overlap with existing constraints
set CUSTOM_PLACE_OPT_PRE_SCRIPT ""      ;# An optional Tcl file; if specified, will be sourced right before the place_opt core command;
                                        ;# review place_opt_icc.tcl script for exact location where this is sourced to avoid overlap with existing constraints
set CUSTOM_PLACE_OPT_POST_SCRIPT ""     ;# An optional Tcl file; if specified, will be sourced right after the place_opt core command;
                                        ;# review place_opt_icc.tcl script for exact location where this is sourced to avoid overlap with existing constraints
set CUSTOM_CLOCK_OPT_CCD_PRE_SCRIPT ""          ;# An optional Tcl file; if specified, will be sourced right before the clock_opt -concurrent_clock_and_data core command;
                                                ;# review clock_opt_ccd_icc.tcl script for exact location where this is sourced to avoid overlap with existing constraints
set CUSTOM_CLOCK_OPT_CCD_POST_SCRIPT ""         ;# An optional Tcl file; if specified, will be sourced right after the clock_opt -concurrent_clock_and_data core command;
                                                ;# review clock_opt_ccd_icc.tcl script for exact location where this is sourced to avoid overlap with existing constraints
set CUSTOM_CLOCK_OPT_ROUTE_PRE_SCRIPT ""  ;# An optional Tcl file; if specified, will be sourced before the route_group -all_clock_nets command;
                                        ;# review clock_opt_route_icc.tcl script for exact location where this is sourced to avoid overlap with existing constraints
set CUSTOM_CLOCK_OPT_ROUTE_PRE_CTO_SCRIPT ""  ;# An optional Tcl file; if specified, will be sourced before the optimize_clock_tree command;
                                        ;# review clock_opt_route_icc.tcl script for exact location where this is sourced to avoid overlap with existing constraints
set CUSTOM_CLOCK_OPT_ROUTE_POST_CTO_SCRIPT ""  ;# An optional Tcl file; if specified, will be sourced after the optimize_clock_tree command;
                                        ;# review clock_opt_route_icc.tcl script for exact location where this is sourced to avoid overlap with existing constraints
set CUSTOM_ROUTE_PRE_SCRIPT ""                  ;# An optional Tcl file; if specified, will be sourced before the route_opt -initial_route_only command;
                                        ;# review route_icc.tcl script for exact location where this is sourced to avoid overlap with existing constraints
set CUSTOM_ROUTE_POST_SCRIPT ""                 ;# An optional Tcl file; if specified, will be sourced after the route_opt -initial_route_only command;
                                        ;# review route_icc.tcl script for exact location where this is sourced to avoid overlap with existing constraints
set CUSTOM_ROUTE_OPT_PRE_SCRIPT ""      ;# An optional Tcl file; if specified, will be sourced right before the route_opt core command;
                                        ;# review route_opt_icc.tcl script for exact location where this is sourced to avoid overlap with existing constraints
set CUSTOM_ROUTE_OPT_POST_SCRIPT ""     ;# An optional Tcl file; if specified, will be sourced right after the route_opt core command;
                                        ;# review route_opt_icc.tcl script for exact location where this is sourced to avoid overlap with existing constraints
set CUSTOM_FOCAL_OPT_PRE_SCRIPT ""      ;# An optional Tcl file; if specified, will be sourced before the focal_opt core commands;
                                        ;# review focal_opt_icc.tcl script for exact location where this is sourced to avoid overlap with existing constraints
set CUSTOM_FOCAL_OPT_POST_SCRIPT ""     ;# An optional Tcl file; if specified, will be sourced after the focal_opt core commands;
                                        ;# review focal_opt_icc.tcl script for exact location where this is sourced to avoid overlap with existing constraints
set CUSTOM_CHIP_FINISH_POST_SCRIPT ""   ;# An optional Tcl file; if specified, will be sourced before the route_opt -inc -size_only command;
                                        ;# review chip_finish_icc.tcl script for exact location where this is sourced to avoid overlap with existing constraints
# ELMOS: added custom script to metal fill step
set CUSTOM_METAL_FILL_PRE_SCRIPT ""

###############################
## Floorplan Input Variables
###############################
set ICC_FLOORPLAN_INPUT   "USER_FILE"   ;# DEF | FP_FILE | CREATE | USER_FILE | SKIP; "DEF" reads $ICC_IN_DEF_FILE; "FP_FILE" reads ICC_IN_FLOORPLAN_FILE;
;# "CREATE" uses create_floorplan command; "USER_FILE" sources $ICC_IN_FLOORPLAN_USER_FILE;
;# "SKIP" skips floorplanning section
set ICC_IN_DEF_FILE             ""      ;# Complete floorplan file in DEF format
set ICC_IN_SPG_DEF_FILE                 ""      ;# Standard cell placement in DEF format from DC for Physical Guidance flow.
                                        ;# The default naming convention for this file from DC-RM is ${DESIGN_NAME}.mapped.std_cell.def
set ICC_IN_FLOORPLAN_FILE       ""      ;# Complete floorplan file generated by write_floorplan 
set ICC_IN_FLOORPLAN_USER_FILE          ""      ;# Complete floorplan file generated by user; This file will simply be sourced.
set ICC_IN_PIN_PAD_PHYSICAL_CONSTRAINTS_FILE ""  ;# I/O constraint file generated by write_pin_pad_physical_constraints which contains pin or pad information
                                        ;# applied prior to create_floorplan command   
set ICC_IN_PHYSICAL_ONLY_CELLS_CREATION_FILE "" ;# a file to include physical-only cell creation commands to be sourced
                                                ;# e.g. create_cell {vdd1left vdd1right vdd1top vdd1bottom} pvdi
set ICC_IN_PHYSICAL_ONLY_CELLS_CONNECTION_FILE "" ;# a file to include physical-only cell connection commands to be sourced
                                                  ;# e.g. derive_pg_connection -power_net $MW_POWER_NET -power_pin $MW_POWER_PORT -ground_net $MW_GROUND_NET -ground_pin $MW_GROUND_PORT -cells {vdd1left vdd1right vdd1top vdd1bottom}

set ICC_PHYSICAL_CONSTRAINTS_FILE   ""  ;# script to add incremental floorplan constraints which will be sourced after read_def, read_floorplan, or floorplan creation
set CUSTOM_CONNECT_PG_NETS_SCRIPT   ""      ;# script for customized derive_pg_connection commands which replaces the default derive_pg_connection commands in the scripts

###############################
## Timing Variables
###############################
set ICC_APPLY_RM_DERATING               FALSE   ;# TRUE|FALSE; when set to FALSE, the derating is assumed to be set in the SDC
set ICC_LATE_DERATING_FACTOR            1.05    ;# Late derating factor, used for both data and clock
set ICC_EARLY_DERATING_FACTOR           0.95    ;# Early derating factor, used for both data and clock

set ICC_APPLY_RM_UNCERTAINTY_PRECTS     FALSE  ;# TRUE|FALSE; when set to TRUE, user uncertainty will be replaced by $ICC_UNCERTAINTY_PRECTS
set ICC_APPLY_RM_UNCERTAINTY_POSTCTS    FALSE  ;# TRUE|FALSE; when set to TRUE, user uncertainty will be replaced by $ICC_UNCERTAINTY_POSTCTS
set ICC_UNCERTAINTY_PRECTS_FILE         ""     ;# Pre-cts uncertainty file used during place_opt
set ICC_UNCERTAINTY_POSTCTS_FILE        ""     ;# Post-cts uncertainty file used during post-CTS optimization and route_opt
set ICC_MAX_TRANSITION                  ""     ;# max_transition value set on the design
set ICC_CRITICAL_RANGE                  ""     ;# critical_range set on the design; default = 50% of each clock period
set ICC_MAX_FANOUT                      ""     ;# max_fanout value set on the design
# ELMOS: changed to HIGH, to better correlate ICC and PT
set ICC_ARNOLDI_EFFORT                  "HIGH"        ;# HIGH|HYBRID|MEDIUM|LOW  Default is MEDIUM which runs a combination of Arnoldi and Elmore for postroute delay calculation. 
                                                ;# When set to HIGH, it will enable full Arnoldi postroute delay calculation. 
                                                ;# When set to HYBRID, it will enable a combination of AWE and Arnoldi postroute delay calculation for faster runtime with comparable accuracy to full Arnoldi.
                                                ;# When set to LOW, postroute delay calculation will only use AWE.
set ICC_PREROUTE_AWE_EFFORT     "NONE"  ;# HIGH|MEDIUM|LOW|NONE By default preroute delay calculation uses Elmore. Setting this variable to HIGH, MEDIUM, or LOW will enable AWE for preroute delay calculation at different effort levels.

set ICC_IN_AOCV_TABLE_FILE      ""      ;# A file containing advanced on-chip variation (OCV) derate factor tables written out by PrimeTime's write_binary_aocvm command 
                                        ;# If specified, it will be read right before clock_opt -only_psyn command at clock_opt_psyn_icc step and AOCV analysis will be enabled
                                        ;# In the Concurrent Clock and Data flow it will be read before any clock_opt command is called at the clock_opt_ccd step

set ICC_AOCV_SCENARIO_MAPPING           ""      ;# A list of scenarios and the AOCV table file for each specified scenario. e.g "{scenario_1 aocv_file_1} {scenario_2 aocv_file_2} ..."
                                                ;# If specifying scenario specific AOCV data, uncomment the timing_library_derate_is_scenario_specific application variable at the end of this script. 
                                                ;# If design level or hierarchical cell level AOCV data is to be applied, put this AOCV file as the final file to be read in. 
                                                ;# e.g. "{scenario_1 aocv_file_1} {scenario_2 aocv_file_} ... {scenario_n design_aocv_file}"


#################################################
## Multicorner-Multimode (MCMM) Input Variables                             
#################################################
set ICC_MCMM_SCENARIOS_FILE             ""       ;# A file containing scenario definitions - examples in rm_icc_scripts/mcmm.scenarios.example
set ICC_DP_MCMM_SCENARIOS_FILE          "$ICC_MCMM_SCENARIOS_FILE" ;# a file that defines a subset of scenarios; default is to be same as $ICC_MCMM_SCENARIOS_FILE;
                                                 ;# $ICC_MCMM_SCENARIOS_FILE is the file that defines your complete set of scenarios which should be used during on-demand netlist creation in the create_odl_dp step;
                                                 ;# $ICC_DP_MCMM_SCENARIOS_FILE allows you to use only subset of scenarios after on-demand netlist creation for design planning tasks up to but 
                                                 ;# not including budgeting then before budgeting in pin_assignment_budgeting_dp step, $ICC_MCMM_SCENARIOS_FILE will be restored 
set ICC_MCMM_PLACE_OPT_SCENARIOS        ""       ;# list of scenarios to be made active during place_opt; optional; by default all scenarios will be made active
set ICC_MCMM_CLOCK_OPT_CCD_SCENARIOS    ""       ;# list of scenarios to be make active during concurent clock and data optimization.  At least one timing critical scenarios with cts_mode=true and setup=true
set ICC_MCMM_CLOCK_OPT_CCD_TIMING_CRITICAL_SCENARIO   "func_min"       ;# timing critical scenario to be used for certain useful skew components in CCD flow  
set ICC_MCMM_CLOCK_OPT_ROUTE_SCENARIOS  ""       ;# list of scenarios to be made active during clock routing; optional; by default all scenarios will be made active
set ICC_MCMM_ROUTE_SCENARIOS            ""       ;# list of scenarios to be made active during signal routing; optional; by default all scenarios will be made active
set ICC_MCMM_ROUTE_OPT_SCENARIOS        ""       ;# list of scenarios to be made active during route_opt; optional; by default all scenarios will be made active
set ICC_MCMM_CHIP_FINISH_SCENARIOS      ""       ;# list of scenarios to be made active during route_opt post chipfinish; optional; by default all scenarios will be made active
set ICC_MCMM_METAL_FILL_SCENARIOS       ""       ;# list of scenarios to be made active during metal filling; optional; by default all scenarios will be made active
set ICC_MCMM_FOCAL_OPT_SCENARIOS        ""       ;# list of scenarios to be made active during focal_opt; optional; by default all scenarios will be made active

##########################################
## In-Design Rail Analysis Flow Variables
##########################################
set PRIMERAIL_DIR               ""                          ;# path to PrimeRail executable.  Required if PrimeRail path is not defined in Unix
set PRIMERAIL_ANALYSIS_INPUT_CEL        $ICC_PLACE_OPT_CEL          ;# input CEL view to run in-design rail analysis.
set PRIMERAIL_ANALYSIS_RAIL             TRUE                        ;# TRUE|FALSE ; will perform static/dynamic rail analysis when TRUE
set PRIMERAIL_ANALYSIS_EM               FALSE                       ;# TRUE|FALSE ; will perform power electromigration analysis when TRUE
set PRIMERAIL_ANALYSIS_INTEGRITY        TRUE                        ;# TRUE|FALSE ; will perform integrity analysis when TRUE
set PRIMERAIL_ANALYSIS_CUSTOM_SCRIPT    ""                          ;# custom script to launch in in-design rail analysis
set PRIMERAIL_ANALYSIS_MODE             "static"                    ;# static | dynamic | dynamic_vectorfree: Specifies the analysis mode used by analyze_rail
set PRIMERAIL_PAD_INSTANCE_FILE         ""                          ;# Only for top level design with power pads. Specify the file with a list of power pad instances, this file format is different from IC Compiler PAD master file
set PRIMERAIL_PAD_MASTER_FILE           ""                          ;# Only for top level design with power pads. Specify the file with a list of power pad masters, this file format is different from IC Compiler PAD instance file
set PRIMERAIL_WORK_DIR                  "PrimeRail_analysis"        ;# in-design rail analysis results directory
set PRIMERAIL_USE_PINS_AS_PADS          TRUE                        ;# TRUE|FALSE ; set to TRUE for blocks which do not have PADS
set PRIMERAIL_ANALYSIS_NETS             "${MW_POWER_NET} ${MW_GROUND_NET}" ;# target PG net names
set PRIMERAIL_SDC_FILE                  ""                          ;# SDC file name.
set PRIMERAIL_SPEF_FILE                 ""                          ;# SPEF file name.
set PRIMERAIL_SWITCHING_ACTIVITY_FILE   ""                          ;# {type (vcd | saif | user-defined) file name" strip path} e.g. "vcd inputs/leon.vcd tb/leon"
set PRIMERAIL_SCRIPT_ONLY               FALSE                       ;# TRUE|FALSE ; will generate and write out PrimeRail script when TRUE
set PRIMERAIL_PACKAGING_FILE            ""                          ;# spice file name containing the package parasitics.
set PRIMERAIL_HOST_MACHINE              ""                          ;# hostname for remote run
set PRIMERAIL_VD_THRESHOLD              ""                          ;# threshold for voltage drop.
set PRIMERAIL_CONFIG_FILE               ""                          ;# PrimeRail configuration file.
set PRIMERAIL_SIGNAL_PARASITICS_FORMAT  ""                          ;# SPEF ; SBPF is default.
set PRIMERAIL_POWER_SCALE_FACTOR        ""                          ;# factor for power scaling.
set PRIMERAIL_POWER_SCALE_VALUE         ""                          ;# value for power scaling.
set PRIMERAIL_WRITE_RAIL_DATA           ""                          ;# {{type file_name [limit]} ...} Writes rail analysis output data from the current session into text files. 
                                                                    ;# Select a type, output file name, and optionally the limit of how many max elements to report.
                                                                    ;# Available types: instance_power, pg_pin_power, voltage_drop_or_rise, effective_voltage_drop_or_rise, minimum_path_resistance, pg_pin_peak_current
                                                                    ;# Example: set PRIMERAIL_WRITE_RAIL_DATA {{instance_power PR_inst_pwr.rpt 100} {voltage_drop_or_rise PR_v_drop_or_rise.rpt}}
set PRIMERAIL_VIA_ARRAY_PARTITION_SIZE  ""                          ;# Specifies how to partition via arrays into resistors by pair lists of via names and partition sizes. 
                                                                    ;# e.g. { {via_layer1 partition_size1} {via_layer2 partition_size2} ...} 
set PRIMERAIL_REUSE_POWER               FALSE                       ;# TRUE|FALSE ; will reuse power analysis results when TRUE
set PRIMERAIL_REUSE_PG_EXTRACTION       FALSE                       ;# TRUE|FALSE ; will reuse PG extraction results when TRUE
set PRIMERAIL_REUSE_SETUP_VARIABLES     FALSE                       ;# TRUE|FALSE ; will reuse setup variables when TRUE
set PRIMERAIL_REUSE_SETUP_FILES         FALSE                       ;# TRUE|FALSE ; will reuse setup files when TRUE
set PRIMERAIL_REUSE_SIGNAL_EXTRACTION   FALSE                       ;# TRUE|FALSE ; will reuse signal extraction when TRUE
set PRIMERAIL_ASSIGN_POWER              FALSE                       ;# TRUE|FALSE ; will perform power analysis based on user provided cell instance power when TRUE
set PRIMERAIL_ANALYSIS_START_TIME       ""                          ;# Specifies the start time of the simulation for dynamic or dynamic_vectorfee analysis modes
set PRIMERAIL_ANALYSIS_END_TIME         ""                          ;# Specifies the end time of the simulation for dynamic or dynamic_vectorfee analysis modes
set PRIMERAIL_OPERATING_CONDITIONS      ""                          ;# If the current design doesn't contain default operation conditions in the first library of the link library, they must be set.

#######################################
## Clock Tree Synthesis (CTS) Variables
#######################################
set ICC_CTS_RULE_NAME   "iccrm_clock_double_spacing" ;# specify the name of a clock nondefault routing rule that you have defined (for ex, in common_cts_settings_icc.tcl); 
                                        ;# it will be associated with set_clock_tree_options -routing_rule  
                                        ;# If ICC_CTS_RULE_NAME is set to iccrm_clock_double_spacing, double spacings will be applied to all layers
set ICC_CTS_LAYER_LIST          ""      ;# clock tree layers, usually M3 and above; e.g. set ICC_CTS_LAYER_LIST "M3 M4 M5"
set ICC_CTS_REF_LIST    				[exec getPrjCfg.rb -r $TECH  tech/phys/cts_cells]      ;# cells for CTS; a space-deliminated list: cell1 cell2 
set ICC_CTS_REF_DEL_INS_ONLY  			[exec getPrjCfg.rb -r $TECH  tech/phys/cts_delay_cells]      ;# cells for CTS delay insertion; a space-deliminated list: cell1 cell2
set ICC_CTS_REF_SIZING_ONLY  	""      ;# cells for CTS sizing only; a space-deliminated list: cell1 cell2 
set ICC_CTS_SHIELD_RULE_NAME  	""      ;# specify clock shielding rule name; requires $ICC_CTS_SHIELD_SPACINGS, $ICC_CTS_SHIELD_WIDTHS to be also specified    
set ICC_CTS_SHIELD_SPACINGS  	""      ;# specify clock shielding spacing associated with shielding rule; a list of layer name and spacing pairs
set ICC_CTS_SHIELD_WIDTHS  	""      ;# specify clock shielding width associated with shielding rule: a list of layer name and width pair
set ICC_CTS_SHIELD_CLK_NAMES  	""      ;# optionally specify a subset of clock names to apply the clock shielding rule: $ICC_CTS_SHIELD_RULE_NAME;
                                        ;# if not specified, $ICC_CTS_SHIELD_RULE_NAME will be applied to all clock nets 

set ICC_CTS_INTERCLOCK_BALANCING  FALSE ;# TRUE|FALSE; set TRUE to enable -inter_clock_balance for "clock_opt -only_cts" at clock_opt_cts_icc task;
                                        ;# specify $ICC_CTS_INTERCLOCK_BALANCING_OPTIONS_FILE to set the options  
set ICC_CTS_INTERCLOCK_BALANCING_OPTIONS_FILE  "" ;# an optional file which contains set_inter_clock_delay_options commands
set ICC_CTS_UPDATE_LATENCY  FALSE               ;# set TRUE to perform clock latency update post CTS
set ICC_CTS_LATENCY_OPTIONS_FILE  ""    ;# an optional file which specifies the latency adjustment options

set ICC_CTS_LOW_POWER_PLACEMENT  FALSE          ;# TRUE|FALSE; set TRUE to enable low power placement for CTS; requires $POWER_OPTIMIZATION to be TRUE to be effective.
set ICC_CTS_CLOCK_GATE_MERGE     FALSE          ;# TRUE|FALSE; set TRUE to enable clock gate merging for CTS for power reduction; requires $POWER_OPTIMIZATION to be TRUE to be effective.
set ICC_CTS_CLOCK_GATE_SPLIT     FALSE          ;# TRUE|FALSE; set TRUE to enable clock gate splitting for CTS for reducing enable pin violations; requires $POWER_OPTIMIZATION to be TRUE to be effective.
set ICC_CTS_SELF_GATING          FALSE          ;# TRUE|FALSE; set TRUE to insert XOR self-gating logic during clock tree synthesis before clock tree construction
                                        ;# An optional gate-level SAIF file ($ICC_IN_SAIF_FILE) is recommended in order to provide clock activity information
set ICC_IN_SAIF_FILE            "$DESIGN_NAME.saif" ;# An optional gate-level SAIF file for self-gating ($ICC_CTS_SELF_GATING)
set ICC_SAIF_INSTANCE_NAME      $DESIGN_NAME  ;# the instance in the SAIF file containing switching activity

set ICC_POST_CLOCK_ROUTE_CTO  FALSE             ;# set TRUE if to perform post route clock tree optimization after clock routing at clock_opt_route_icc step

#########################################
## Routing and Chipfinishing Variables
#########################################
## end cap cells
set ICC_H_CAP_CEL                  ""           ;# defines the horizontal CAP CELL library cell
set ICC_V_CAP_CEL                  ""           ;# defines the vertical CAP CELL library cell (for the Well Proximity Effect)

## redundant via insertion (ICC_DBL_VIA) options
# ELMOS: LOW -> HIGH
set ICC_DBL_VIA_FLOW_EFFORT      HIGH            ;# LOW|MED|HIGH  - MED enables concurrent soft-rule redundant via insertion
                                                ;# HIGH runs another redundant via, timing driven, after chipfinishing
set ICC_CUSTOM_DBL_VIA_DEFINE_SCRIPT ""         ;# script to define the redundant via definitions
set ICC_DBL_VIA_DURING_INITIAL_ROUTING TRUE  ;# TRUE|FALSE - TRUE enables automatic redundant via insertion after detail route change of "route_opt -initial"
                                        ;# FALSE runs insert_zrt_redundant_vias after "route_opt -initial"

## antenna fixing (ICC_FIX_ANTENNA) options
# ELMOS: get rules from TECHXML
set ANTENNA_RULES_FILE           [exec getPrjCfg.rb -r $TECH -p tech/phys/antenna]             ;# defines the antenna rules

set ICC_USE_DIODES               TRUE           ;# TRUE|FALSE; control variable to allow diodes to be inserted both by the 
                                                ;# insert_port_protection_diodes command as well as the router
# ELMOS: get rules from TECHXML
set ICC_ROUTING_DIODES           [exec getPrjCfg.rb -r $TECH tech/phys/diode]             ;# space separated list of diode names
set ICC_PORT_PROTECTION_DIODE    [exec getPrjCfg.rb -r $TECH tech/phys/port_prot]         ;# diode name for insert_port_protection_diodes
                                        ;# Format = library_name/diode_name

set ICC_PORT_PROTECTION_DIODE_EXCLUDE_PORTS ""  ;# a list of ports to be excluded by insert_port_protection_diodes

## filler cell insertion (ADD_FILLER_CELL) options
# ELMOS: 
set FILLER_CELL_METAL            "[exec getPrjCfg.rb -r $TECH tech/phys/decaps]"             ;# space separated list of filler cells with metals
set FILLER_CELL                  "[exec getPrjCfg.rb -r $TECH tech/phys/filler]"             ;# space separated list of filler cells 
# Elmos: override this variable in layout.tcl if you have additional pyhsical only cells which should be writen out in LVS verilog netlist
# e.g ENDCAP cells in ELMOS0U35 technology
set OUTPUT_REFERENCES		 "$FILLER_CELL_METAL"
## signal em
set ICC_FIX_SIGNAL_EM    FALSE          ;# TRUE|FALSE; set TRUE to enable signal em fixing; please uncomment the section and follow instruction in chip_finish_icc.tcl
set ICC_TLUPLUS_SIGNAL_EM_FILE  ""              ;# The TLU+ file with the advanced signal EM constraints in it to be read by read_signal_em_constraints. This may be the same as the standard TLU+ files.
set ICC_ITF_SIGNAL_EM_FILE      ""    ;# The ITF file with the advanced signal EM constraints to be read by the read_signal_em_constraints -itf_em command in chip_finish_icc.tcl

###############################
## Emulation TLUplus Files
###############################
## Note : emulated metal fill may not correlate well with real metal fill, especially for advanced technology nodes.
#  Use it for reference only.
set TLUPLUS_MAX_EMULATION_FILE         ""    ;#  Max TLUplus file
set TLUPLUS_MIN_EMULATION_FILE         ""    ;#  Min TLUplus file

###############################
## check_signoff_correlation  Variables
###############################
set PT_DIR ""                                   ;# path to PrimeTime bin directory
set PT_SDC_FILE ""                              ;# optional file in case PrimeTime has a different SDC that what is available in the IC Compiler database
set STARRC_DIR ""                               ;# path to StarRC bin directory
set STARRC_MAX_NXTGRD ""                        ;# MAX NXTGRD file
set STARRC_MIN_NXTGRD ""                        ;# MIN NXTGRD file
set STARRC_MAP_FILE "$MAP_FILE"                 ;# NXTGRD mapping file, defaults to TLUPlus mapping file, but could be different

set ICC_SIGNOFF_OPT_CHECK_CORRELATION_POSTROUTE_SCRIPT "" ;# a file to be sourced to run at check_signoff_correlation end of route_opt_icc step; 
                                                  ;# example - rm_icc_scripts/signoff_opt_check_correlation_postroute_icc.example.tcl

#######################################
## Metal fill and Signoff DRC Variables
#######################################
## For IC Validator metal Fill - ensure environment variable PRIMEYIELD_HOME_DIR is set and that IC Validator is included in the same path where the IC Compiler shell is executed from
## For IC Validator DRC - ensure environment variable ICV_HOME_DIR is set and that IC Validator is included in the same path where the IC Compiler shell is executed from

set SIGNOFF_FILL_RUNSET ""                      ;# IC Validator runset for signoff_metal_fill command
# ELMOS: 
set SIGNOFF_DRC_RUNSET  "[exec getPrjCfg.rb -r $TECH tech/tools/drc/script]"                      ;# IC Validator runset for signoff_drc command
set SIGNOFF_MAPFILE     ""                      ;# IC Validator mapping file for signoff_metal_fill and signoff_drc commands
set ICC_ECO_SIGNOFF_DRC_MODE  "NONE"            ;# NONE|AUTO_ECO determines whether signoff_drc will run in the Auto ECO flow mode.

## Options for signoff_metal_fill command using ICV engine in metal_fill_icc.tcl
set SIGNOFF_METAL_FILL_TIMING_DRIVEN FALSE    ;# TRUE|FALSE : set this to TRUE to enable timing driven for IC Validator metal fill
set TIMING_PRESERVE_SLACK_SETUP  "0.1"                  ;# float : setup slack threshold for timing driven ICV metal fill; default 0.1
                                        ;# also used by wire_spreading/widening in chip_finishi_icc.tcl
set TIMING_PRESERVE_SLACK_HOLD "0"              ;# float : hold slack threshold for wire_spreading/widening in chip_finishi_icc.tcl; default 0
## Options for insert_metal_fill command using ICC engine in metal_fill_icc.tcl
set ICC_METAL_FILL_SPACE           2            ;# space amount used during the IC Compiler insert_metal_fill command
set ICC_METAL_FILL_TIMING_DRIVEN  TRUE          ;# enables timing driven metal fill for the IC Compiler insert_metal_fill command

###############################
## focal_opt Variables
###############################
set ICC_FOCAL_OPT_HOLD_VIOLS     "all"          ;# filename|all - blank to skip; filename to fix violations from a file; specify "all" to fix all hold violations
set ICC_FOCAL_OPT_SETUP_VIOLS    ""              ;# filename|all - blank to skip; filename to fix violations from a file; specify "all" to fix all setup violations
set ICC_FOCAL_OPT_DRC_NET_VIOLS  "all"          ;# filename|all - blank to skip; filename to fix violations from a file; specify "all" to fix all DRC net violations
set ICC_FOCAL_OPT_DRC_PIN_VIOLS  ""             ;# filename|all - blank to skip; filename to fix violations from a file; specify "all" to fix all DRC pin violations
set ICC_FOCAL_OPT_XTALK_VIOLS    ""             ;# filename - blank to skip; filename to fix crosstalk violations from a file
set ICC_FOCAL_OPT_CCD            FALSE          ;# FALSE|TRUE - Setting to TRUE performs additional postroute concurrent clock and data optimization on all setup endpoints

###############################
## ECO Flow Variables
###############################
# ELMOS: change to FREEZE_SILICON
set ICC_ECO_FLOW        "FREEZE_SILICON"  ;# NONE|UNCONSTRAINED|FREEZE_SILICON
                                        ;# UNCONSTRAINED : NO spare cell insertion ; cells can be added (pre tapeout)
                                        ;# FREEZE_SILICON : spare cell insertion/freeze silicon ECO
# ELMOS: standard script to insert spare cells
set ICC_SPARE_CELL_FILE         "custom_spare_cells.tcl"       ;# Tcl script to insert the spare cells, e.g. :
                                         ;# insert_spare_cells -lib_cell {INV8 DFF1} -cell_name spares -num_instances 300
set ICC_ECO_FILE                ""       ;# a verilog netlist or Tcl file containing ECO changes - specify the file name and type of file using ICC_ECO_FLOW_TYPE
set ICC_ECO_FLOW_TYPE   "verilog" ;# verilog | pt_drc_setup_fixing_tcl | pt_hold_fixing_tcl | pt_minimum_physical_impact - specify type of ECO file for UNCONSTRAINED ICC_ECO_FLOW;
                                  ;# depending on the value specified, the commands used to read ECO file and place ECO cells vary;
                                  ;# specify verilog if you provide a functional eco file for ICC_ECO_FILE;
                                  ;# specify pt_drc_setup_fixing_tcl if you provide a change file generated by the PrimeTime fix_eco_drc or fix_eco_timing -setup commands;
                                  ;# specify pt_hold_fixing_tcl if you provide a change file generated by the PrimeTime fix_eco_timing -hold command
                                  ;# specify pt_minimum_physical_impact if you provide a change file generated by the PrimeTime fix_eco_timing  or fix_eco_leakage command 
# ELMOS:
set ICC_ECO_METAL_FILL_MODE  "signoff_stage" ;# early_stage | signoff_stage; only ICV is supported;
                                      ;# specify early stage to use ICV DRC based metal fill trimming (faster);
                                      ;# specify signoff_stage to perform complete ICV metal fill purge, ADR and metal fill insertion  
set ICC_ECO_AUTO_ECO_METAL_FILL "FALSE"       ;# FALSE | TRUE: Specifies whether the automatic ECO will be used for ECO metal fill operations. 
                                              ;# This will effect both early_stage and signoff_stage of ICC_ECO_METAL_FILL_MODE  


########################################################################################################################
############                        IC COMPILER DESIGN PLANNING SPECIFIC                         #######################
############(variables for IC Compiler Design Planning and IC Compiler Hierarchical Reference Methodologies)  ##########
########################################################################################################################

########################################################################################################################
## Common variables (applied to both IC Compiler Design Planning and IC Compiler Hierarchical Reference Methodologies )
########################################################################################################################

set ICC_DP_VERBOSE_REPORTING    FALSE           ;# TRUE|FALSE; generate additional reports before placement
set ICC_DP_SET_HFNS_AS_IDEAL_THRESHOLD  ""              ;# integer; specify a threshold to set nets with fanout larger than it as ideal nets
set ICC_DP_SET_MIXED_AS_IDEAL   TRUE            ;# TRUE|FALSE; set mixed clock/signal paths as ideal nets

set ICC_DP_FIX_MACRO_LIST       ""              ;# ""|skip|"a_list_of_macros"; unfix all macros OR skip fix OR fix specified macros before placement
# ELMOS: standard script
set CUSTOM_ICC_DP_PLACE_CONSTRAINT_SCRIPT "custom_dp_script.tcl"            ;# Put your set_keepout_margin and fp_set_macro_placement_constraint in this file
set CUSTOM_ICC_DP_PREROUTE_STD_CELL_SCRIPT ""   ;# File to perform customized preroute_standard_cell commands

## PNS and PNA control variables
set CUSTOM_ICC_DP_PNS_CONSTRAINT_SCRIPT ""              ;# File to add PNS constraints which is loaded before running PNS
set PNS_POWER_NETS              "${MW_POWER_NET} ${MW_GROUND_NET}" ;# Target nets for PNS; syntax is "your_power_net your_ground_net"
set PNS_POWER_BUDGET            1000            ;# Unit in milliWatts; default is 1000
set PNS_VOLTAGE_SUPPLY          1.5             ;# Unit in Volts; default is 1.5
set PNS_VIRTUAL_RAIL_LAYER      ""              ;# Specify the metal layer you want to use as virtual rail
set PNS_OUTPUT_DIR              "./pna_output"  ;# Output directory for PNS and PNA output files
set PNA_TLUPLUS_MAX_FILE        ""              ;# String; for hierarchical on-demand-loading (ODL) MCMM flow, it is required to specify a valid $PNA_TLUPLUS_MAX_FILE
set PNA_TLUPLUS_MIN_FILE        ""              ;# or $PNA_TLUPLUS_MIN_FILE for PNA or it will fail.
set PNA_EXTRACTION_TEMPERATURE  ""              ;# Float; set the wire extraction temperature for PNA. Optional.
set PNA_EXTRACTION_CORNER       ""              ;# min|max; set the parasitic corner for RC extraction for PNA. Optional.

###############################################################
## IC Compiler Hierarchical Reference Methodology Variables
###############################################################

set ICC_DP_PLAN_GROUPS          "$HIERARCHICAL_CELLS"   ;# full module names from which plan groups will be created
                                                        ;#   space deliminated list: "top/A top/B top/C"
                                                ;# default to $HIERARCHICAL_CELLS from common_setup.tcl if using Design Compiler Topographical
set ICC_DP_PLANGROUP_FILE               ""              ;# floorplan file containing plan group creation and location which should be the output of write_floorplan

set ICC_DP_ALLOW_FEEDTHROUGH          FALSE             ;# TRUE|FALSE; allow feedthrough creation during pin assignment

# ELMOS: standard script
set CUSTOM_ICC_DP_PNS_SCRIPT    "icc_dp_tpns.tcl"              ;# customized PNS script; replacing PNS section in scripts; for template based PNS, this is required
set CUSTOM_ICC_DP_PNA_SCRIPT    ""              ;# customized PNA script; replacing PNA section in scripts

## DFT-aware hierarchical design planning variables
set ICC_DP_DFT_FLOW             FALSE           ;# TRUE|FALSE; enable DFT-aware hierarchical design planning flow; requires ICC_IN_FULL_CHIP_SCANDEF_FILE
set ICC_IN_FULL_CHIP_SCANDEF_FILE "$DESIGN_NAME.mapped.expanded.scandef"        
                                                ;# full-chip SCANDEF file for DFT-aware hierarchical design planning flow (see $ICC_DP_DFT_FLOW)
                                                ;# used only in hierarchical design planning phase; not used or needed for block level implementations and top level assembly 

set BUDGETING_SDC_OUTPUT_DIR            "./sdc" ;# budgeting SDC output directory; default is "./sdc"

## ODL flow variables
set ICC_DP_ODL_BLOCK_MCMM_MAP_FILE      "rm_icc_dp_scripts/odl_block_mcmm_map_file"
set ICC_DP_ODL_HOST_OPTION   ""                 ;# lsf|grd|samehost|list_of_hosts; this controls the set_host_options value for create_on_demand_netlist
                                                        ;# if either lsf or grd is specified, you must also specify $ICC_DP_ODL_HOST_OPTION_SUBMIT_OPTIONS 
                                                        ;# if list_of_hosts is specified, you must also specify $ICC_DP_ODL_HOST_OPTION_HOSTS_LIST 

set ICC_DP_ODL_HOST_OPTION_SUBMIT_OPTIONS {}    ;# controls the value of -submit_option option for set_host_options for create_on_demand_netlist command. 
                                                ;# If ICC_DP_ODL_HOST_OPTION is set to lsf, 
                                                ;# then lsf specific submit options should be specified, for example, 
                                                ;# {-q bnormal -R "rusage\[mem=12000\]\cputype==emt64 cpuspeed==EMT3000 qsc==e"}

set ICC_DP_ODL_HOST_OPTION_HOSTS_LIST  ""              ;# a list of hosts on which to perform create_on_demand_netlist

## TIO and block abstraction variables
set ICC_BLOCK_ABSTRACTIONS_LIST         ""              ;# a list of all the block abstractions used in the design;
                                                ;# if left empty, the list will be auto set to include all soft macros in the design if you are following HRM step-by-step 

set ICC_TIO_BLOCK_LIST                  $ICC_BLOCK_ABSTRACTIONS_LIST
                                                ;# a list of names of block abstractions that are to be optimized by transparent interface optimization (TIO) at route_opt_icc;
                                                ;# you can change it to a subset of block abstractions before route_opt_icc starts  

set ICC_TIO_OPTIMIZE_BLOCK_INTERFACE    TRUE            ;# TRUE|FALSE; set TRUE for TIO to optimize interface logic
set ICC_TIO_OPTIMIZE_MIM_BLOCK_INTERFACE FALSE          ;# TRUE|FALSE; set TRUE for TIO to optimize inside MIM blocks; set true only when you are opening MIM blocks for TIO
set ICC_TIO_OPTIMIZE_SHARED_LOGIC       FALSE           ;# TRUE|FALSE; set TRUE for TIO to optimize shared logic; requires $ICC_TIO_OPTIMIZE_BLOCK_INTERFACE to be also enabled
set ICC_TIO_BLOCK_UPDATE_SETUP_SCRIPT  ""               ;# Script for block abstraction setup, useful for variable settings during block update. To be used during set_top_implementation_options -block_update_setup_script ICC_TIO_BLOCK_UPDATE_SETUP_SCRIPT.  The file name should not include relative paths

set ICC_TIO_HOST_OPTION         ""              ;# lsf|grd|samehost|list_of_hosts; this controls the set_host_options value for TIO
                                                        ;# if either lsf or grd is specified, you must also specify $ICC_TIO_HOST_OPTION_SUBMIT_OPTIONS 
                                                        ;# if list_of_hosts is specified, you must also specify $ICC_TIO_HOST_OPTION_HOSTS_LIST
                                                ;# Please note that if $ICC_TIO_OPTIMIZE_BLOCK_INTERFACE is set to TRUE and $ICC_TIO_BLOCK_LIST is not empty,
                                                ;# which are both default for HRM, you should also specify a valid value for $ICC_TIO_HOST_OPTION
                
set ICC_TIO_HOST_OPTION_SUBMIT_OPTIONS {}       ;# controls the value of -submit_option option for set_host_options for TIO 
                                                ;# If $ICC_TIO_HOST_OPTION is set to lsf, 
                                                ;# then lsf specific submit options should be specified and vice versa, for example, 
                                                ;# {-q bnormal -R "rusage\[mem=12000\]\cputype==emt64 cpuspeed==EMT3000 qsc==e"}

set ICC_TIO_HOST_OPTION_HOSTS_LIST  ""              ;# a list of hosts on which to perform automatic block update during TIO


set ICC_TIO_WRITE_ECO_FILE              FALSE   ;# TRUE|FALSE; set TRUE for TIO to write out an ECO file to TIO_eco_changes directory

set ICC_IMPLEMENTATION_PHASE    default         ;# default|block|top; set it to block or top to disable tasks such as Milkyway design library creation,
                                                ;# importing of black boxes, scenario creation, voltage area creation, and power switch creation, etc 
                                                ;# in init_design_icc.tcl which should have been completed during design planning phase and should be skipped during 
                                                ;# block and top level implementation phases; also set it to top to enable TIO at route_opt_icc task;
                                                ;# if you are following IC Compiler Hierarchical RM step-by-step, please do not change this;
                                                ;# it will be automatically set to block or top for block or top level designs, respectively
  
set MW_SOFT_MACRO_LIBS                  ""         ;# a list containing paths to all block libraries; they will be added as reference libraries of the top level library
                                                ;# if you are following IC Compiler Hierarchical RM step-by-step, please do not change this;
                                                ;# it will be automatically set to include all block libraries in the design for top level implementation

###############################################################################
## IC Compiler Design Planning Reference Methodology (Flat) Variables
###############################################################################

## explore mode: flow control variables
# ELMOS: FALSE
set ICC_DP_EXPLORE_MODE                 FALSE   ;# TRUE|FALSE; turn on exploration mode
set ICC_DP_EXPLORE_STYLE                default ;# valid options are: default | placement_only | no_pns_pna | no_ipo
                                                ;# default: place -> PNS/PNA -> in-place optimization -> final groute, snapshot, QoR, timing, and outputs 
                                                ;# placement_only: skips pns/pna and in-place optimization from default | no_pns_pna: skips pna/pns from default 
                                                ;# | no_ipo: skips in-place optimization from default 
set ICC_DP_EXPLORE_SAVE_CEL_EACH_STEP    FALSE  ;# TRUE|FALSE; save 3 additional CEL after placement, in-place optimization, and PNS in explore mode (requires more disk space)
set ICC_DP_EXPLORE_REPORTING_EACH_STEP   FALSE  ;# TRUE|FALSE; generate QoR snapshot and timing report after each step (longer run time)
set ICC_DP_EXPLORE_USE_GLOBAL_ROUTE      FALSE
set ICC_DP_EXPLORE_SAVE_CEL_AFTER_GROUTE TRUE   ;# TRUE|FALSE; save 2 additional CEL after global route: one after placement and one at the end
set ICC_DP_EXPLORE_CUSTOM_PG_SCRIPT  ""         ;# string; script to be loaded to create customized PG straps after placement in explore mode; 
                                                ;# valid only if ICC_DP_EXPLORE_STYLE is placement_only or no_pns_pna

## explore mode: additional PNS control variables
set PNS_TARGET_VOLTAGE_DROP       250           ;# Unit in milliVolts. Tool default is 10% of PNS_POWER_BUDGET
# ELMOS: TRUE
set PNS_BLOCK_MODE              TRUE           ;# TRUE|FALSE; specify if the design is block or top level; It turns on correspondant options in PNS and PNA
set PNS_PAD_MASTERS             ""              ;# Only for top level design with power pads. Specify cell masters for power pads, e.g. "pv0i.FRAM pv0a.FRAM"
set PNS_PAD_INSTANCE_FILE       ""              ;# Only for top level design with power pads. Specify the file with a list of power pad instances
set PNS_PAD_MASTER_FILE         ""              ;# Only for top level design with power pads. Specify the file with a list of power pad masters
## Please provide only one of PNS_PAD_MASTERS, OR PNS_PAD_INSTANCE_FILE, OR PNS_PAD_MASTER_FILE

#####################################################################################################################################
## NO NEED TO CHANGE THE FOLLOWING IF Design Compiler Reference Metholodgy IS USED PRIOR TO IC Compiler Reference Methodology
#####################################################################################################################################
set ICC_IN_VERILOG_NETLIST_FILE "$DESIGN_NAME.mapped.v" ;#1 to n verilog input files, spaced by blanks
set ICC_IN_SDC_FILE             "$DESIGN_NAME.mapped.sdc"
set ICC_IN_DDC_FILE             "$DESIGN_NAME.mapped.ddc"
set ICC_IN_UPF_FILE             "$DESIGN_NAME.mapped.upf"
set ICC_IN_SCAN_DEF_FILE        "$DESIGN_NAME.mapped.scandef"              ;# default from Design Compiler Reference Metholodgy is $DESIGN_NAME.mapped.scandef
set MW_DESIGN_LIBRARY           "${DESIGN_NAME}_LIB"    ;# Milkyway design library
set COPY_FROM_MW_DESIGN_LIBRARY ""              ;# specify a milkyway design library if you want reference methodology to copy it as MW_DESIGN_LIBRARY
                                                ;# only applies if ICC_INIT_DESIGN_INPUT is set to Milkyway


set REPORTS_DIR                 "reports"               ;# Directory to write reports.
set RESULTS_DIR                 "results"               ;# Directory to write output data files
set SOURCE_DIR                  $RESULTS_DIR            ;# Source directory for analysis tasks such as FM and MVRC

set REPORTS_DIR_INIT_DESIGN                     $REPORTS_DIR
set REPORTS_DIR_PLACE_OPT                       $REPORTS_DIR
set REPORTS_DIR_CLOCK_OPT_CCD                   $REPORTS_DIR
set REPORTS_DIR_CLOCK_OPT_ROUTE                 $REPORTS_DIR
set REPORTS_DIR_ROUTE                           $REPORTS_DIR
set REPORTS_DIR_ROUTE_OPT                       $REPORTS_DIR
set REPORTS_DIR_CHIP_FINISH                     $REPORTS_DIR
set REPORTS_DIR_ECO                          $REPORTS_DIR
set REPORTS_DIR_FOCAL_OPT                       $REPORTS_DIR
set REPORTS_DIR_SIGNOFF_OPT                     $REPORTS_DIR
set REPORTS_DIR_METAL_FILL                      $REPORTS_DIR
set REPORTS_DIR_DP                              $REPORTS_DIR
set REPORTS_DIR_DP_CREATE_PLANGROUPS    $REPORTS_DIR
set REPORTS_DIR_DP_ROUTEABILITY_ON_PLANGROUPS   $REPORTS_DIR
set REPORTS_DIR_DP_PIN_ASSIGNMENT_BUDGETING     $REPORTS_DIR
set REPORTS_DIR_DP_COMMIT                       $REPORTS_DIR
set REPORTS_DIR_DP_PREPARE_BLOCK                $REPORTS_DIR
set REPORTS_DIR_FORMALITY               $REPORTS_DIR

if { ! [file exists $REPORTS_DIR_INIT_DESIGN] } { file mkdir $REPORTS_DIR_INIT_DESIGN }
if { ! [file exists $REPORTS_DIR_PLACE_OPT] } { file mkdir $REPORTS_DIR_PLACE_OPT }
if { ! [file exists $REPORTS_DIR_CLOCK_OPT_CCD] } { file mkdir $REPORTS_DIR_CLOCK_OPT_CCD }
if { ! [file exists $REPORTS_DIR_CLOCK_OPT_ROUTE] } { file mkdir $REPORTS_DIR_CLOCK_OPT_ROUTE }
if { ! [file exists $REPORTS_DIR_ROUTE] } { file mkdir $REPORTS_DIR_ROUTE }
if { ! [file exists $REPORTS_DIR_ROUTE_OPT] } { file mkdir $REPORTS_DIR_ROUTE_OPT }
if { ! [file exists $REPORTS_DIR_CHIP_FINISH] } { file mkdir $REPORTS_DIR_CHIP_FINISH }
if { ! [file exists $REPORTS_DIR_ECO] } { file mkdir $REPORTS_DIR_ECO }
if { ! [file exists $REPORTS_DIR_FOCAL_OPT] } { file mkdir $REPORTS_DIR_FOCAL_OPT }
if { ! [file exists $REPORTS_DIR_SIGNOFF_OPT] } { file mkdir $REPORTS_DIR_SIGNOFF_OPT }
if { ! [file exists $REPORTS_DIR_METAL_FILL] } { file mkdir $REPORTS_DIR_METAL_FILL }
if { ! [file exists $REPORTS_DIR_DP] } { file mkdir $REPORTS_DIR_DP }
if { ! [file exists $REPORTS_DIR_DP_CREATE_PLANGROUPS] } { file mkdir $REPORTS_DIR_DP_CREATE_PLANGROUPS }
if { ! [file exists $REPORTS_DIR_DP_ROUTEABILITY_ON_PLANGROUPS] } { file mkdir $REPORTS_DIR_DP_ROUTEABILITY_ON_PLANGROUPS }
if { ! [file exists $REPORTS_DIR_DP_PIN_ASSIGNMENT_BUDGETING] } { file mkdir $REPORTS_DIR_DP_PIN_ASSIGNMENT_BUDGETING }
if { ! [file exists $REPORTS_DIR_DP_COMMIT] } { file mkdir $REPORTS_DIR_DP_COMMIT }
if { ! [file exists $REPORTS_DIR_DP_PREPARE_BLOCK] } { file mkdir $REPORTS_DIR_DP_PREPARE_BLOCK }
if { ! [file exists $REPORTS_DIR_FORMALITY] } { file mkdir $REPORTS_DIR_FORMALITY }

set REPORTS_DIR_IN_DESIGN_RAIL                  $REPORTS_DIR
if { ! [file exists $REPORTS_DIR_IN_DESIGN_RAIL] } { file mkdir $REPORTS_DIR_IN_DESIGN_RAIL }

## Logical libraries
set_app_var search_path  ". ./rm_icc_scripts ./rm_icc_zrt_scripts ./rm_icc_dp_scripts ./$RESULTS_DIR $ADDITIONAL_SEARCH_PATH $search_path"

# #############
# ELMOS: add rm-script locations to search_path
set_app_var search_path  "$env(PROJECT_HOME)/scripts/layout/tcl/icc/rm_icc_scripts $search_path"
set_app_var search_path  "$env(PROJECT_HOME)/scripts/layout/tcl/icc/rm_icc_zrt_scripts $search_path"
set_app_var search_path  "$env(PROJECT_HOME)/scripts/layout/tcl/icc/rm_icc_dp_scripts $search_path"
set_app_var search_path  "../syn/results $search_path"
# import: user_tcl should have highest priority
set_app_var search_path  "./user_tcl $search_path"
# #############

# ELMOS: these variables are not existing in fm_shell 
if {$synopsys_program_name ne "fm_shell"} {
  if {$synopsys_program_name != "mvrc" || $synopsys_program_name != "vsi" || $synopsys_program_name != "vcst"} {
      set_app_var target_library  "$TARGET_LIBRARY_FILES"
      set_app_var link_library  "* $TARGET_LIBRARY_FILES $ADDITIONAL_LINK_LIB_FILES"
  } else {
      set_app_var link_library  "$TARGET_LIBRARY_FILES $ADDITIONAL_LINK_LIB_FILES"
  }
}

if { ! [file exists $RESULTS_DIR] } {
    file mkdir $RESULTS_DIR
}
if { ! [file exists $REPORTS_DIR] } {
    file mkdir $REPORTS_DIR
}

if {$synopsys_program_name == "icc_shell"} {

## Min/Max library relationships
#  For "set_operating_conditions -analysis_type on_chip_variation", it is not recommended if only -max is specified.
#  (such as in rm_icc_scripts/mcmm.scenarios.example) 
#  Only use it if both -max and -min of set_operating_conditions are specified and point to two different libraries
#  and are characterized to model OCV effects of the same corner.
if {$MIN_LIBRARY_FILES != "" } {
  foreach {max_library min_library} $MIN_LIBRARY_FILES {
    set_min_library $max_library -min_version $min_library
  }
}

## Reference libraries
if { ![file exists [which $MW_REFERENCE_CONTROL_FILE]]} {
 if {[file exists $MW_DESIGN_LIBRARY/lib]} {
   set_mw_lib_reference $MW_DESIGN_LIBRARY -mw_reference_library "$MW_REFERENCE_LIB_DIRS $MW_SOFT_MACRO_LIBS"
 }
}

## PD4 is not always used
if {![info exists PD4]} {set PD4 ""}

## Avoiding too many messages
set_message_info -id PSYN-040 -limit 10 ;# Dont_touch for fixed cells
set_message_info -id PSYN-087 -limit 10 ;# Port inherits its location from pad pin
set_message_info -id LINT-8   -limit 10 ;# input port is unloaded

set_app_var check_error_list "$check_error_list LINK-5 PSYN-375"

}

if {$synopsys_program_name == "fm_shell"} {
    set_app_var sh_new_variable_message false
}

## Uncomment this variable if you wish for specified library cell derates set
# with the set_timing_derate command or AOCV data for library cells to be saved
# in the Milkyway database.
# When true, this variable will enable any derates specified on library cells to
# be saved to the Milkyway database:
#
# set_app_var timing_save_library_derate true

## Uncomment this variable to make set_timing_derate and read_aocvm only applied
# to the current scenario for settings related to library cell objects :
#  set_app_var timing_library_derate_is_scenario_specific true

#################################################################################

puts "RM-Info: Completed script [info script]\n"
