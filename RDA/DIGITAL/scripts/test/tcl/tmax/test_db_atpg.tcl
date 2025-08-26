puts "-------------------------------------------------------------------------------"
puts "RM-Info: Running script [info script]"
puts "-------------------------------------------------------------------------------"

##################################################################
# TetraMAX Reference Methodology Main Script                     #
# Script: tmax.tcl                                               #
# Version: O-2018.06-SP2 (October 8, 2018)                       #
# Copyright (C) 2008-2018 Synopsys, Inc. All rights reserved.    #
##################################################################

## ELMOS: initialize variables if not defined
##        
check_var COVERAGE_DB_ATPG            "100"
check_var LIMIT_DB_ATPG               "10"
check_var CUSTOM_DB_ADD_FAULTS_SCRIPT ""

##################################################################
#    DB_ATPG: Create Patterns for Dynamic Bridging Fault Test    #
##################################################################
set PATTERN_NAME "dynbr"

## ELMOS: replaced persistent_fault_model flow by using external pattern
##        and added a variable for the abort limit
## set_faults -bridge_inputs
## set_atpg -abort_limit 10

## ELMOS: define fault model and re-simulate previous pattern
remove_faults -all
set_faults -bridge_inputs
set_faults -model dynamic_bridging

if {$CUSTOM_DB_ADD_FAULTS_SCRIPT != ""} {
   source -echo $CUSTOM_DB_ADD_FAULTS_SCRIPT
} else {
   add_faults -node_file ${NODE_FILE}
}

report_summaries faults
read_external_pattern $EXTERNAL_PATTERN_TYPES

## ELMOS: added variable for ATPG coverage
set_atpg -coverage $COVERAGE_DB_ATPG

## ELMOS: added variable (optional list) for ATPG limit
set_atpg -abort_limit [lindex $LIMIT_DB_ATPG 0] ; #use first element from list
set ADDITIONAL_LIMITS [lreplace $LIMIT_DB_ATPG 0 0] ; #remove first element from list


report_settings atpg
report_settings simulation
report_settings delay
if { $TMAX_DEBUG_MODE } {
   report_settings -all > ${REPORTS_DIR}/${DESIGN_NAME}_dynbr_atpg_settings.${tmax_file_ext}.rpt
}

run_atpg -auto_compression

# Additional runs with increased abort limits may improve coverage
## ELMOS: added configurable loop for additional runs
foreach limit $ADDITIONAL_LIMITS {
   set_atpg -abort_limit $limit
   run_atpg -auto_compression
}
#set_atpg -abort_limit 100
#run_atpg -auto_compression
#set_atpg -abort_limit 1000
#run_atpg -auto_compression

## ELMOS: replaced faults writing by common procedure -> "write_results"
## # Dynamic bridging patterns are included in the transistion delay patterns.
## # Don't write them out yet.
## write_faults ${RESULTS_DIR}/${DESIGN_NAME}_dynbr_post.${tmax_file_ext}.faults.gz -all -replace -compress gzip
write_results ${PATTERN_NAME}

# Dynamic bridging patterns are included in the transistion delay patterns.
# Don't report on them yet.

## ELMOS: replaced persistent_fault_model flow by using external pattern
##if { !($TMAX_DIRECT_CREDIT) } {
##   set_faults -model transition
##   run_fault_sim
##   report_summaries faults
##}

# Dynamic bridging patterns are included in the transistion delay patterns.
# Don't fault simulate for static bridging faults yet.

# Dynamic bridging patterns are included in the transistion delay patterns.
# Don't fault simulate for stuck-at faults yet.

puts "-------------------------------------------------------------------------------"
puts "RM-Info: Completed script [info script]"
puts "-------------------------------------------------------------------------------"
