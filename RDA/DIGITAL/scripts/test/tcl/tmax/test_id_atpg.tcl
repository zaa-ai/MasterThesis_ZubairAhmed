puts "-------------------------------------------------------------------------------"
puts "RM-Info: Running script [info script]"
puts "-------------------------------------------------------------------------------"

## ELMOS: initialize variables if not defined
##        
check_var COVERAGE_ID_ATPG            "100"
check_var LIMIT_ID_ATPG               "10"
check_var CUSTOM_ID_ADD_FAULTS_SCRIPT ""

##################################################################
#          ID_ATPG: Create Patterns for IDDQ Fault Test          #
##################################################################
set PATTERN_NAME "iddq"

remove_faults -all
set_faults -model iddq

if {$CUSTOM_ID_ADD_FAULTS_SCRIPT != ""} {
   source -echo $CUSTOM_ID_ADD_FAULTS_SCRIPT
} else {
   add_faults -all
}

report_summaries faults

# ELMOS: switch to tmax1 for IDDQ (STAR 3666545)
set_atpg -num_threads 0
set_simulation -num_threads 0
set_atpg -num_processes 1
set_simulation -num_processes 1

# ELMOS: added variable for ATPG coverage
set_atpg -coverage $COVERAGE_ID_ATPG

# ELMOS: added variable (optional list) for ATPG limit
set_atpg -abort_limit [lindex $LIMIT_ID_ATPG 0] ; #use first element from list
set ADDITIONAL_LIMITS [lreplace $LIMIT_ID_ATPG 0 0] ; #remove first element from list

# ELMOS: maximum number of IDDQ strobes
set_atpg -patterns 15 -basic_min_detects_per_pattern 1000
set_atpg -merge high

# ELMOS: allows BUS gates (pads) to be at Z state while IDDQ measure
set_iddq nofloat

report_settings atpg
report_settings simulation

if { $TMAX_DEBUG_MODE } {
   report_settings -all > ${REPORTS_DIR}/${DESIGN_NAME}_iddq_atpg_settings.${tmax_file_ext}.rpt
}

run_atpg -auto_compression

# Additional runs with increased abort limits may improve coverage
# ELMOS: added configurable loop for additional runs
foreach limit $ADDITIONAL_LIMITS {
   set_atpg -abort_limit $limit
   run_atpg -auto_compression
}

write_results ${PATTERN_NAME}

puts "-------------------------------------------------------------------------------"
puts "RM-Info: Completed script [info script]"
puts "-------------------------------------------------------------------------------"
