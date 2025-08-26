# #####################################################
# Flow Version 3
# #####################################################
# digital.mcmm.scenarios.tcl
# $Date: 2016-02-03 11:31:15 +0100 (Wed, 03 Feb 2016) $
# $Rev: 2188 $:
# $Author: rk $
# #####################################################
#################################################################################
# Design Compiler MCMM Scenarios Setup File Reference
# Script: dc.mcmm.scenarios.tcl
# Version: H-2013.03-SP2 (August 5, 2013)
# Copyright (C) 2011-2013 Synopsys, Inc. All rights reserved.
#################################################################################

#################################################################################
# This is an example of the MCMM scenarios setup file for Design Compiler.
# Please note that this file will not work as given and must be edited for your
# design.
#
# Create this file for each design in your MCMM flow and configure the filename
# with the value of the ${DCRM_MCMM_SCENARIOS_SETUP_FILE} in
# rm_setup/dc_setup_filenames.tcl
#
# It is recommended to use a minimum set of worst case setup scenarios
# and a worst case leakage scenario in Design Compiler.
# Further refinement to optimize across all possible scenarios is recommended
# to be done in IC Compiler.
#################################################################################

#################################################################################
# Additional Notes
#################################################################################
#
# In MCMM, good leakage and dynamic power optimization results can be obtained by
# using a worst case leakage scenario along with scenario-independent clock gating
# (compile_ultra -gate_clock)
#
# A recommended scenario naming convention (used by Lynx) is the following:
#
# <MM_TYPE>.<OC_TYPE>.<RC_TYPE>
#
# MM_TYPE - Label that identifies the operating mode or set of timing constraints
#           Example values: mode_norm, mode_slow, mode_test
#
# OC_TYPE - Label that identifies the library operating conditions or PVT corner
#           Example values: OC_WC, OC_BC, OC_TYP, OC_LEAK, OC_TEMPINV
#
# RC_TYPE - Label that identifies an extraction corner (TLUPlus files)
#           Example values: RC_MAX_1, RC_MIN_1, RC_TYP
#################################################################################

#################################################################################

# The following procedure is used to control the naming of the scenario-specific
# MCMM input and output files.
# By default the naming convention inserts the scenario name before the file
# extension.
# Modify this procedure if you want to use different name convention for the
# scenario-specific file naming.

proc dcrm_mcmm_filename { filename scenario } {
    return [file rootname $filename].$scenario[file extension $filename]
}

proc set_max_libs {} {
    global SRAM_MAX_LIB
    global SRAM_MAX_OC
    global OTP_MAX_LIB
    global OTP_MAX_OC
    global IPS_MAX_LIB
    global IPS_MAX_OC

    set_operating_conditions -library tcb018gbwp7twc WCCOM
    set_operating_conditions -library $SRAM_MAX_LIB  $SRAM_MAX_OC
    set_operating_conditions -library $OTP_MAX_LIB   $OTP_MAX_OC
    set_operating_conditions -library $IPS_MAX_LIB   $IPS_MAX_OC

}

proc set_min_libs {} {
    global SRAM_MIN_LIB
    global SRAM_MIN_OC
    global OTP_MIN_LIB
    global OTP_MIN_OC
    global IPS_MIN_LIB
    global IPS_MIN_OC

    set_operating_conditions -library tcb018gbwp7tlt  LTCOM
    set_operating_conditions -library $SRAM_MIN_LIB  $SRAM_MIN_OC
    set_operating_conditions -library $OTP_MIN_LIB   $OTP_MIN_OC
    set_operating_conditions -library $IPS_MIN_LIB   $IPS_MIN_OC

}

set DCRM_CONSTRAINTS_INPUT_FILE                         sdc/${DESIGN_NAME}.constraints.tcl

#################################################################################
# Worst Case Setup Scenario NORMAL
#################################################################################

set scenario mode_norm.oc_wc.rc_max
if {[lsearch [all_scenarios] $scenario] >= 0} {
    remove_scenario ${scenario}
}
create_scenario ${scenario}
# Read in scenario-specific constraints file

puts "RM-Info: Sourcing script file [which [dcrm_mcmm_filename ${DCRM_CONSTRAINTS_INPUT_FILE} ${scenario}]]\n"
source [dcrm_mcmm_filename ${DCRM_CONSTRAINTS_INPUT_FILE} ${scenario}]

# puts "RM-Info: Reading SDC file [which [dcrm_mcmm_filename ${DCRM_SDC_INPUT_FILE} ${scenario}]]\n"
# read_sdc [dcrm_mcmm_filename ${DCRM_SDC_INPUT_FILE} ${scenario}]

set_max_libs

set_tlu_plus_files -max_tluplus $TLUPLUS_MAX_FILE  \
    -tech2itf_map ${MAP_FILE}

check_tlu_plus_files

# Include scenario specific SAIF file, if possible, for power analysis.
# Otherwise, the default toggle rate of 0.1 will be used for propagating
# switching activity.

# read_saif -auto_map_names -input ${DESIGN_NAME}.${scenario}.saif -instance < DESIGN_INSTANCE > -verbose

# Set options for worst case setup scenario
set_scenario_options -setup true -hold false -leakage_power false

report_scenario_options

#################################################################################
# Best Case Hold Scenario NORMAL
#################################################################################

set scenario mode_norm.oc_bc.rc_min
if {[lsearch [all_scenarios] $scenario] >= 0} {
    remove_scenario ${scenario}
}
create_scenario ${scenario}

# Read in scenario-specific constraints file

puts "RM-Info: Sourcing script file [which [dcrm_mcmm_filename ${DCRM_CONSTRAINTS_INPUT_FILE} ${scenario}]]\n"
source [dcrm_mcmm_filename ${DCRM_CONSTRAINTS_INPUT_FILE} ${scenario}]

# puts "RM-Info: Reading SDC file [which [dcrm_mcmm_filename ${DCRM_SDC_INPUT_FILE} ${scenario}]]\n"
# read_sdc [dcrm_mcmm_filename ${DCRM_SDC_INPUT_FILE} ${scenario}]

set_min_libs

set_tlu_plus_files -max_tluplus $TLUPLUS_MIN_FILE  \
    -tech2itf_map ${MAP_FILE}

check_tlu_plus_files

# Set options for worst case setup scenario
set_scenario_options -setup false -hold true -leakage_power false

report_scenario_options

#################################################################################
# Worst Case Setup Scenario  TEST
#################################################################################

set scenario mode_test.oc_wc.rc_max
if {[lsearch [all_scenarios] $scenario] >= 0} {
    remove_scenario ${scenario}
}
create_scenario ${scenario}

# Read in scenario-specific constraints file

puts "RM-Info: Sourcing script file [which [dcrm_mcmm_filename ${DCRM_CONSTRAINTS_INPUT_FILE} ${scenario}]]\n"
source [dcrm_mcmm_filename ${DCRM_CONSTRAINTS_INPUT_FILE} ${scenario}]

# puts "RM-Info: Reading SDC file [which [dcrm_mcmm_filename ${DCRM_SDC_INPUT_FILE} ${scenario}]]\n"
# read_sdc [dcrm_mcmm_filename ${DCRM_SDC_INPUT_FILE} ${scenario}]

#
set_max_libs

set_tlu_plus_files -max_tluplus $TLUPLUS_MAX_FILE  \
    -tech2itf_map ${MAP_FILE}

check_tlu_plus_files

# Set options for worst case setup scenario
set_scenario_options -setup true -hold false -leakage_power false

report_scenario_options

#################################################################################
# Best Case Hold Scenario TEST
#################################################################################

set scenario mode_test.oc_bc.rc_min
if {[lsearch [all_scenarios] $scenario] >= 0} {
    remove_scenario ${scenario}
}
create_scenario ${scenario}

# Read in scenario-specific constraints file

puts "RM-Info: Sourcing script file [which [dcrm_mcmm_filename ${DCRM_CONSTRAINTS_INPUT_FILE} ${scenario}]]\n"
source [dcrm_mcmm_filename ${DCRM_CONSTRAINTS_INPUT_FILE} ${scenario}]

# puts "RM-Info: Reading SDC file [which [dcrm_mcmm_filename ${DCRM_SDC_INPUT_FILE} ${scenario}]]\n"
# read_sdc [dcrm_mcmm_filename ${DCRM_SDC_INPUT_FILE} ${scenario}]

set_min_libs

set_tlu_plus_files -max_tluplus $TLUPLUS_MIN_FILE  \
    -tech2itf_map ${MAP_FILE}

check_tlu_plus_files

# Set options for worst case setup scenario
set_scenario_options -setup false -hold true -leakage_power false

report_scenario_options

