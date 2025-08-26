# ELMOS: removed, has to be sourced from main synthesis script
#source -echo -verbose ./rm_setup/dc_setup.tcl

#################################################################################
# Design Compiler Reference Methodology Script for Top-Down MCMM Flow
# Script: dc.tcl
# Version: S-2021.06  
# Copyright (C) 2007-2021 Synopsys, Inc. All rights reserved.
#################################################################################

# Design Compiler must be run in topographical mode for MCMM flow support
# MCMM also requires a license for Design Compiler Graphical
if {![shell_is_in_topographical_mode]} {
  puts "RM-Error: dc_shell must be run in topographical mode for MCMM support."
  exit 1
}

# Design Compiler must be run in topographical mode for SPG flow support
# SPG also requires a license for Design Compiler Graphical
if {![shell_is_in_topographical_mode]} {
  puts "RM-Error: dc_shell must be run in topographical mode for SPG support."
  exit 1
}

#################################################################################
# Additional Variables
#
# Add any additional variables needed for your flow here.
#################################################################################


################################################################################
# You can enable inference of multibit registers from the buses defined in the RTL.
# The replacement of single-bit cells with multibit library cells occurs during execution 
# of the compile_ultra command. This variable has to be set before reading the RTL
#
# set_app_var hdlin_infer_multibit default_all
#################################################################################

if { $OPTIMIZATION_FLOW == "hplp" } {
set_app_var hdlin_infer_multibit default_all
}

# Enable the support of via resistance for RC estimation to improve the timing 
# correlation with IC Compiler
set_app_var spg_enable_via_resistance_support true

if {[file exists [which ${LIBRARY_DONT_USE_PRE_COMPILE_LIST}]]} {
  puts "RM-Info: Sourcing script file [which ${LIBRARY_DONT_USE_PRE_COMPILE_LIST}]\n"
  source -echo -verbose $LIBRARY_DONT_USE_PRE_COMPILE_LIST
}

#################################################################################
# Setup for Formality Verification
#################################################################################

# In the event of an inconclusive (or hard) verification, we recommend using
# the set_verification_priority commands provided from the analyze_points command
# in Formality. The set_verification_priority commands target specific
# operators to reduce verification complexity while minimizing QoR impact.
# The set_verification_priority commands should be applied after the design
# is read and elaborated.

# For designs that don't have tight QoR constraints and don't have register retiming,
# you can use the following variable to enable the highest productivity single pass flow.
# This flow modifies the optimizations to make verification easier.
# This variable setting should be applied prior to reading in the RTL for the design.

# set_app_var simplified_verification_mode true

# For more information about facilitating formal verification in the flow, refer
# to the following SolvNet article:
# "Resolving Inconclusive and Hard Verifications in Design Compiler"
# https://solvnet.synopsys.com/retrieve/033140.html

# Define the verification setup file for Formality
set_svf ${RESULTS_DIR}/${DCRM_SVF_OUTPUT_FILE}

#################################################################################
# Setup SAIF Name Mapping Database
#
# Include an RTL SAIF for better power optimization and analysis.
#
# saif_map should be issued prior to RTL elaboration to create a name mapping
# database for better annotation.
################################################################################

saif_map -start

#################################################################################
# Read in the RTL Design
#
# Read in the RTL source files or read in the elaborated design (.ddc).
#################################################################################

define_design_lib WORK -path ./WORK

###The following variable helps verification when there are differences between DC and FM while inferring logical hierarchies 
set_app_var hdlin_enable_hier_map true



# Modify the following autoread defaults if desired

#set_app_var hdlin_autoread_verilog_extensions       ".v"; 
#set_app_var hdlin_autoread_sverilog_extensions      ".sv .sverilog"; 
#set_app_var hdlin_autoread_vhdl_extensions          ".vhd .vhdl";

# Note: When autoread is used ${RTL_SOURCE_FILES} can include a list of
#       both directories and files.

# ELMOS: added exclude option
analyze -autoread \
        -rebuild \
        -recursive \
        -exclude ${AUTOREAD_EXCLUDE_LIST} \
        -top ${DESIGN_NAME} \
        -output_script ${RESULTS_DIR}/${DCRM_AUTOREAD_RTL_SCRIPT} \
        ${RTL_SOURCE_FILES}

elaborate ${DESIGN_NAME}

set_verification_top

# OR

# You can read an elaborated design from the same release.
# Using an elaborated design from an older release will not give the best results.

# read_ddc ${DCRM_ELABORATED_DESIGN_DDC_OUTPUT_FILE}
write -hierarchy -format ddc -output ${RESULTS_DIR}/${DCRM_ELABORATED_DESIGN_DDC_OUTPUT_FILE}
