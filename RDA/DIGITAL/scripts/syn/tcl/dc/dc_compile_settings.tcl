#################################################################################
# sets the multibit_mode attribute
#################################################################################
if { $OPTIMIZATION_FLOW == "hplp"} {
  # Enable mapping to multibit only if the timing is not degraded. Adjust the critical Range as required by the design.
    set_multibit_options -mode timing_only -critical_range 0.1
}

#################################################################################
# Reports pre-synthesis congestion analysis.
#################################################################################
if { $OPTIMIZATION_FLOW == "hc"} {
  #Analyze the RTL constructs which may lead to congestion
  analyze_rtl_congestion > ${REPORTS_DIR}/${DCRM_ANALYZE_RTL_CONGESTION_REPORT_FILE}
}

#################################################################################
# Apply Logical Design Constraints
#################################################################################

# For MCMM, do not apply the constraints here.  Constraints should be
# applied for each scenario in the ${DCRM_MCMM_SCENARIOS_SETUP_FILE}

#################################################################################
# Apply The Operating Conditions
#################################################################################

# For MCMM, do not apply the operating conditions here.  Operating conditions
# should be applied for each scenario in the ${DCRM_MCMM_SCENARIOS_SETUP_FILE}

#################################################################################
# Set Up the Multicorner Multimode (MCMM) Scenarios
#
# Note: The MCMM flow is only supported in topographical mode and it requires
#       a license for Design Compiler Graphical. 
#################################################################################

# Use the dc.mcmm.scenarios.tcl example file as as reference for
# what should be included in the ${DCRM_MCMM_SCENARIOS_SETUP_FILE}

puts "RM-Info: Sourcing script file [which ${DCRM_MCMM_SCENARIOS_SETUP_FILE}]\n"
source -echo -verbose ${DCRM_MCMM_SCENARIOS_SETUP_FILE}

# To get the best memory and runtime performance, only define scenarios
# needed for optimization in Design Compiler.
# If additional scenarios are also included, use the following command to
# select the set of desired scenarios for optimization.

# set_active_scenarios <list of scenarios for synthesis optimization>

report_scenarios > ${REPORTS_DIR}/${DCRM_MCMM_SCENARIOS_REPORT}
# ELMOS: removed, as it fills the report directory with trash
#check_scenarios -output ${REPORTS_DIR}

#################################################################################
# Create Default Path Groups
#
# Separating these paths can help improve optimization.
# Remove these path group settings if user path groups have already been defined.
#################################################################################

set current_scenario_saved [current_scenario]
foreach scenario [all_active_scenarios] {
  current_scenario ${scenario}
  set ports_clock_root [filter_collection [get_attribute [get_clocks] sources] object_class==port]
  group_path -name REGOUT -to [all_outputs] 
  group_path -name REGIN -from [remove_from_collection [all_inputs] ${ports_clock_root}] 
  group_path -name FEEDTHROUGH -from [remove_from_collection [all_inputs] ${ports_clock_root}] -to [all_outputs]
}
current_scenario ${current_scenario_saved}

#################################################################################
# Power Optimization Section
#################################################################################

    #############################################################################
    # Clock Gating Setup
    #############################################################################

    # If your design has instantiated clock gates, you should use identify_clock_gating
    # command to identify and the report_clock_gating -multi_stage to report them.

    # identify_clock_gating
    # report_clock_gating -multi_stage -nosplit > ${REPORTS_DIR}/${DCRM_INSTANTIATE_CLOCK_GATES_REPORT}

    # If you do not want clock-gating to optimize your user instantiated
    # clock-gating cells, you should set the pwr_preserve_cg attribute upon
    # those clock-gating cells.

    # set_preserve_clock_gate [all_clock_gates]

    # Default clock_gating_style suits most designs.  Change only if necessary.
    # set_clock_gating_style -positive_edge_logic {integrated} -negative_edge_logic {integrated} -control_point before ...   

    # Clock gate insertion is now performed during compile_ultra -gate_clock
    # so insert_clock_gating is no longer recommended at this step.

    # The following setting can be used to enable global clock gating.
    # With global clock gating, common enables are extracted across hierarchies
    # which results in fewer redundant clock gates. 

    # set_app_var compile_clock_gating_through_hierarchy true 

    # Allows addition or reduction of stages of clock gates.
    # ie: If RTL ICGs are identified and clock gating style -num_stages is 1 it will enable extraction of new enables
    # which will be combined with RTL ICG enables.

    # set_app_var power_cg_reconfig_stages true 

    # For better timing optimization of enable logic, clock latency for 
    # clock gating cells can be optionally specified.

    # set_clock_gate_latency -clock <clock_name> -stage <stage_num> \
    #         -fanout_latency {fanout_range1 latency_val1 fanout_range2 latency_val2 ...}

    # You can use "set_self_gating_options" command to specify self-gating 
    # options when -self_gating option is used in addition to -gate_clock 
    # option at the compile_ultra command. To inserts self-gate on clock-gated
    # registers, uncomment the following line:
    # set_self_gating_options -interaction_with_clock_gating insert

    # To improve enable timing in high performance designs, physically aware clock gating 
    # is available in Design Compiler topographical for Synopsys Physical Guidance (SPG) 
    # flow. This flow works best with a corresponding IC Compiler  SPG flow. To enable 
    # physically aware clock gating in Design Compiler Graphical, uncomment the 
    # following setting:
    # Note: this setting is overwritten by set_qor_strategy

    # ELMOS: enabled variable
    set_app_var power_cg_physically_aware_cg true
    
    #############################################################################
    # Power Optimization Setup
    #############################################################################

    # For MCMM, do not apply the SAIF file here.  The SAIF file should be read in
    # for each scenario in the ${DCRM_MCMM_SCENARIOS_SETUP_FILE}

    if {[shell_is_in_topographical_mode]} {
      # For multi-Vth design, replace the following to set the threshold voltage groups in the libraries.

      # set_attribute <my_hvt_lib> default_threshold_voltage_group HVT -type string
      # set_attribute <my_lvt_lib> default_threshold_voltage_group LVT -type string
    }

    # Starting in J-2014.09, leakage optimization is the default flow and is always enabled.
    # For MCMM, include a leakage scenario in the ${DCRM_MCMM_SCENARIOS_SETUP_FILE}.

    # Power prediction with clock tree estimation is not supported with MCMM.
    # Do not use the set_power_prediction command with MCMM designs.
 
if {[shell_is_in_topographical_mode]} {

  ##################################################################################
  # Apply Physical Design Constraints
  #
  # Optional: Floorplan information can be read in here if available.
  # This is highly recommended for irregular floorplans.
  #
  # Floorplan constraints can be provided from one of the following sources:
  # * extract_physical_constraints with a DEF file
  #	* read_floorplan with a floorplan file (written by write_floorplan)
  #	* User generated Tcl physical constraints
  #
  ##################################################################################

  # Specify ignored layers for routing to improve correlation
  # Use the same ignored layers that will be used during place and route

  if { ${MIN_ROUTING_LAYER} != ""} {
    set_ignored_layers -min_routing_layer ${MIN_ROUTING_LAYER}
  }
  if { ${MAX_ROUTING_LAYER} != ""} {
    set_ignored_layers -max_routing_layer ${MAX_ROUTING_LAYER}
  }

  report_ignored_layers

  # If the macro names change after mapping and writing out the design due to
  # ungrouping or Verilog change_names renaming, it may be necessary to translate 
  # the names to correspond to the cell names that exist before compile.

  # During DEF constraint extraction, extract_physical_constraints automatically
  # matches DEF names back to precompile names in memory using standard matching rules.
  # read_floorplan will also automatically perform this name matching.

  # Modify set_query_rules if other characters are used for hierarchy separators
  # or bus names. 

  # set_query_rules  -hierarchical_separators {/ _ .} \
  #                  -bus_name_notations {[] __ ()}   \
  #                  -class {cell pin port net}       \
  #                  -wildcard                        \
  #                  -regsub_cumulative               \
  #                  -show

  ## For DEF floorplan input

  # The DEF file for Design Compiler Topographical can be written from IC Compiler using the following 
  # recommended options:
  # icc_shell> write_def -version 5.7 -rows_tracks_gcells -fixed -pins -blockages -specialnets \
  #                      -vias -regions_groups -verbose -output ${DCRM_DCT_DEF_INPUT_FILE}

  if {[file exists [which ${DCRM_DCT_DEF_INPUT_FILE}]]} {
    # If you have physical only cells as a part of your floorplan DEF file, you can use
    # the -allow_physical_cells option with extract_physical_constraints to include
    # the physical only cells as a part of the floorplan in Design Compiler to improve correlation.
    #
    # Note: With -allow_physical_cells, new logical cells in the DEF file
    #       that have a fixed location will also be added to the design in memory.
    #       See the extract_physical_constraints manpage for more information about
    #       identifying the cells added to the design when using -allow_physical_cells.
  
    # extract_physical_constraints -allow_physical_cells ${DCRM_DCT_DEF_INPUT_FILE}

    puts "RM-Info: Reading in DEF file [which ${DCRM_DCT_DEF_INPUT_FILE}]\n"
    if { $OPTIMIZATION_FLOW == "hplp"} {
	extract_physical_constraints -allow_physical_cells ${DCRM_DCT_DEF_INPUT_FILE}  
    } else {
	extract_physical_constraints ${DCRM_DCT_DEF_INPUT_FILE}
    }
  }
  
  # OR

  ## For floorplan file input

  # The floorplan file for Design Compiler Topographical can be written from IC Compiler using the following 
  # recommended options:
  # Note: IC Compiler requires the use of -placement {terminal} with -create_terminal beginning in the
  #       D-2010.03-SP1 release.
  # icc_shell> write_floorplan -placement {io terminal hard_macro soft_macro} -create_terminal \
  #                            -row -create_bound -preroute -track ${DCRM_DCT_FLOORPLAN_INPUT_FILE}

  # Read in the secondary floorplan file, previously written by write_floorplan in Design Compiler,
  # to restore physical-only objects back to the design, before reading the main floorplan file.

  if {[file exists [which ${DCRM_DCT_FLOORPLAN_INPUT_FILE}.objects]]} {
    puts "RM-Info: Reading in secondary floorplan file [which ${DCRM_DCT_FLOORPLAN_INPUT_FILE}.objects]\n"
    read_floorplan ${DCRM_DCT_FLOORPLAN_INPUT_FILE}.objects
  }

  if {[file exists [which ${DCRM_DCT_FLOORPLAN_INPUT_FILE}]]} {
    puts "RM-Info: Reading in floorplan file [which ${DCRM_DCT_FLOORPLAN_INPUT_FILE}]\n"
    read_floorplan ${DCRM_DCT_FLOORPLAN_INPUT_FILE}
  }

  # OR

  ## For Tcl file input

  # For Tcl constraints, the name matching feature must be explicitly enabled
  # and will also use the set_query_rules setttings. This should be turned off
  # after the constraint read in order to minimize runtime.

  if {[file exists [which ${DCRM_DCT_PHYSICAL_CONSTRAINTS_INPUT_FILE}]]} {
    set_app_var enable_rule_based_query true
    puts "RM-Info: Sourcing script file [which ${DCRM_DCT_PHYSICAL_CONSTRAINTS_INPUT_FILE}]\n"
    source -echo -verbose ${DCRM_DCT_PHYSICAL_CONSTRAINTS_INPUT_FILE}
    set_app_var enable_rule_based_query false 
  }


  # Use write_floorplan to save the applied floorplan.

  # Note: A secondary floorplan file ${DCRM_DCT_FLOORPLAN_OUTPUT_FILE}.objects
  #       might also be written to capture physical-only objects in the design.
  #       This file should be read in before reading the main floorplan file.

  write_floorplan -all ${RESULTS_DIR}/${DCRM_DCT_FLOORPLAN_OUTPUT_FILE}

  # Verify that all the desired physical constraints have been applied
  # Add the -pre_route option to include pre-routes in the report
  report_physical_constraints > ${REPORTS_DIR}/${DCRM_DCT_PHYSICAL_CONSTRAINTS_REPORT}
}

#################################################################################
# Apply Additional Optimization Constraints
#################################################################################

# Prevent assignment statements in the Verilog netlist.
set_fix_multiple_port_nets -all -buffer_constants

#################################################################################
# Save the compile environment snapshot for the Consistency Checker utility.
#
# This utility checks for inconsistent settings between Design Compiler and
# IC Compiler which can contribute to correlation mismatches.
#
# Download this utility from SolvNet.  See the following SolvNet article for
# complete details:
#
# https://solvnet.synopsys.com/retrieve/026366.html
#
# The article is titled: "Using the Consistency Checker to Automatically Compare
# Environment Settings Between Design Compiler and IC Compiler"
#################################################################################

# Uncomment the following to snapshot the environment for the Consistency Checker
# for each active scenario.  You will also need to run the Consistency Checker
# utility for each scenario environment snapshot.

# set current_scenario_saved [current_scenario]
# foreach scenario [all_active_scenarios] {
#   current_scenario ${scenario}
#   write_environment -consistency -output ${REPORTS_DIR}/[dcrm_mcmm_filename ${DCRM_CONSISTENCY_CHECK_ENV_FILE} ${scenario}]
# }
# current_scenario ${current_scenario_saved}

#################################################################################
# Check for Design Problems 
#################################################################################

# Check the current design for consistency
check_design -summary
check_design > ${REPORTS_DIR}/${DCRM_CHECK_DESIGN_REPORT}

# The analyze_datapath_extraction command can help you to analyze why certain data 
# paths are no extracted, uncomment the following line to report analyisis.

# analyze_datapath_extraction > ${REPORTS_DIR}/${DCRM_ANALYZE_DATAPATH_EXTRACTION_REPORT}


#################################################################################
# Multibit Register Reports pre-compile_ultra
#################################################################################

#################################################################################
# Uncomment the next line to verify that the desired bussed registers are grouped as multibit components 
# These multibit components are mapped to multibit registers during compile_ultra
#
# redirect ${REPORTS_DIR}/${DCRM_MULTIBIT_COMPONENTS_REPORT} {report_multibit -hierarchical }
#################################################################################
if { $OPTIMIZATION_FLOW == "hplp"} {
    redirect ${REPORTS_DIR}/${DCRM_MULTIBIT_COMPONENTS_REPORT} {report_multibit -hierarchical }
}

# ELMOS: for better timing optimization let the synthesis tool change the size of pure gates, instead of dont_touch
set PURE_CELLS  [get_designs -quiet pure_*] 
if { [sizeof_collection $PURE_CELLS] > 0 } { 
    set_compile_directives $PURE_CELLS -delete_unloaded_gate false -constant_propagation false -local_optimization false -critical_path_resynthesis false
}

