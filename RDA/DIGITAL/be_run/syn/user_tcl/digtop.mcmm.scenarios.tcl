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
    global MAX_LIBRARY_NAME
    global MAX_LIBRARY_OC
    global SRAM_INST
    global SRAM_MAX_LIB
    global SRAM_MAX_OC
    global OTP_INST
    global OTP_MAX_LIB
    global OTP_MAX_OC
    global IPS_INST
    global IPS_MAX_LIB
    global IPS_MAX_OC

    ## On chip variation is used as analysis type for the example.
    #  As -min_library and -min are not specified, the tool uses the max operating condition for -min.
    #  That means tool is modeling on chip variation using the max operating condition and the early and late derating factors for
    #  min and max path delay analysis, respectively.

    set_operating_conditions -analysis_type on_chip_variation \
	-object_list [get_flat_cells $SRAM_INST] \
	-max_library $SRAM_MAX_LIB \
	-max $SRAM_MAX_OC

    set_operating_conditions -analysis_type on_chip_variation \
	-object_list [get_flat_cells $OTP_INST ]  \
	-max_library $OTP_MAX_LIB \
	-max $OTP_MAX_OC

    set_operating_conditions -analysis_type on_chip_variation \
	-object_list [get_flat_cells $IPS_INST ] \
	-max_library $IPS_MAX_LIB \
	-max $IPS_MAX_OC

    set_operating_conditions -analysis_type on_chip_variation \
	-max_library $MAX_LIBRARY_NAME \
	-max $MAX_LIBRARY_OC

}

proc set_min_libs {} {
    global MIN_LIBRARY_NAME
    global MIN_LIBRARY_OC
    global SRAM_INST
    global SRAM_MIN_OC
    global SRAM_MIN_LIB
    global OTP_INST
    global OTP_MIN_OC
    global OTP_MIN_LIB
    global IPS_INST
    global IPS_MIN_OC
    global IPS_MIN_LIB

    ## On chip variation is used as analysis type for the example.
    #  As -min_library and -min are not specified, the tool uses the max operating condition for -min.
    #  That means tool is modeling on chip variation using the max operating condition and the early and late derating factors for
    #  min and max path delay analysis, respectively.

    set_operating_conditions -analysis_type on_chip_variation \
	-object_list [get_flat_cells $SRAM_INST] \
	-max_library $SRAM_MIN_LIB \
	-max $SRAM_MIN_OC

    set_operating_conditions -analysis_type on_chip_variation \
	-object_list [get_flat_cells $OTP_INST ]  \
	-max_library $OTP_MIN_LIB \
	-max $OTP_MIN_OC

    set_operating_conditions -analysis_type on_chip_variation \
	-object_list [get_flat_cells $IPS_INST ] \
	-max_library $IPS_MIN_LIB \
	-max $IPS_MIN_OC

    set_operating_conditions -analysis_type on_chip_variation \
	-max_library $MIN_LIBRARY_NAME \
	-max $MIN_LIBRARY_OC

}

set DCRM_CONSTRAINTS_INPUT_FILE                         sdc/${DESIGN_NAME}.constraints.tcl

#################################################################################
# Worst Case Setup Scenario NORMAL
#################################################################################

change_names -rules verilog -hierarchy

proc set_max_conditions {} {

    global TLUPLUS_MAX_FILE
    global MAP_FILE

    set_max_libs

    set_tlu_plus_files -max_tluplus ${TLUPLUS_MAX_FILE} \
	-tech2itf_map ${MAP_FILE}

    set_scenario_options -setup true -hold false -cts_mode true -cts_corner max
}

proc set_min_conditions {} {

    global TLUPLUS_MIN_FILE
    global MAP_FILE

    set_min_libs

    set_tlu_plus_files -max_tluplus ${TLUPLUS_MIN_FILE} \
	-tech2itf_map ${MAP_FILE}

    set_scenario_options -setup false -hold true
}

source [dcrm_mcmm_filename ${DCRM_CONSTRAINTS_INPUT_FILE} procs]


foreach mode [list func scan] {
    foreach corner [list min max] {
	create_scenario ${mode}_${corner}

	# Read in scenario-specific constraints file
	puts "RM-Info: Sourcing script file [dcrm_mcmm_filename ${DCRM_CONSTRAINTS_INPUT_FILE} ${mode}_${corner}]\n"
	source -echo -verbose [dcrm_mcmm_filename ${DCRM_CONSTRAINTS_INPUT_FILE} ${mode}_${corner}]

	eval set_${corner}_conditions

	check_tlu_plus_files
	report_scenario_options
    }
}

# scenario independent constraints
# additional dont_touches on inputs of otp, to be sure that the placement guide is working
foreach otp {slp_b_tsmc180bcd50_4kx12_cm16d_ab_r20} {
    set otp_inst                [get_cells -hierarchical -filter "ref_name == $otp" *]
    set otp_inputs              [get_flat_pins -filter "pin_direction == in" [get_object_name $otp_inst]/*]
    set all_connected_to_inputs [all_connected -leaf [all_connected $otp_inputs]]
    set only_outputs            [get_flat_pins -filter "pin_direction == out" $all_connected_to_inputs]
    set_dont_touch_network -no_propagate $only_outputs
}

# analog nets
puts "On Following ports set_dont_touch_network -no_propagate will be set:\n"
set DONT_TOUCH_NETWORK [get_ports A_OTP_*]
set_dont_touch_network -no_propagate $DONT_TOUCH_NETWORK

#ToDo: Warum???
#set_dont_touch_network -no_propagate [get_flat_pins -filter "pin_direction == out" -of_objects [all_macro_cells]]

#ToDo:
# for better timing optimization let the synthesis tool change the size of pure gates
# delete all pure cells that drive no loads
#
#set_compile_directives [get_designs pure_*] -delete_unloaded_gate true -constant_propagation false -local_optimization false -critical_path_resynthesis false
# except cells required for SCAN
# set_compile_directives  [get_cells -hierarchical pure_buf_scan_*] -delete_unloaded_gate false

report_timing -scenarios [all_active_scenarios] -loops > ${REPORTS_DIR}/loops.rpt

#set sh_continue_on_error false
