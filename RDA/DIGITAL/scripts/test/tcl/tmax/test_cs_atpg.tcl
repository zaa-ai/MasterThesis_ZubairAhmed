puts "-------------------------------------------------------------------------------"
puts "RM-Info: Running script [info script]"
puts "-------------------------------------------------------------------------------"

## ELMOS: initialize variables if not defined
##        
check_var COVERAGE_CS_ATPG            "100"
check_var LIMIT_CS_ATPG               "10"
check_var CUSTOM_CS_ADD_FAULTS_SCRIPT ""

##################################################################
#  CS_ATPG: Create Patterns for Cell-Aware Stuck-At Fault Test   #
##################################################################
## ELMOS: This script is copied from "test_sa_atpg.tcl" and
##        adapted for Cell Aware
set PATTERN_NAME "cell_stuck"

## ELMOS: replaced persistent_fault_model flow by using external pattern
##        and added a variable for the abort limit
## set_faults -model stuck
## if { $TMAX_DIRECT_CREDIT } {
##    update_faults -direct_credit
##    report_summaries faults
## }
## set_atpg -abort_limit 10

remove_faults -all
read_cell_model ${CELL_MODEL}
set_faults -model stuck

if {$CUSTOM_CS_ADD_FAULTS_SCRIPT != ""} {
   source -echo $CUSTOM_CS_ADD_FAULTS_SCRIPT
} else {
   add_faults -all -cell_aware
}

report_summaries faults
read_external_pattern $EXTERNAL_PATTERN_TYPES

## ELMOS: added variable for ATPG coverage
set_atpg -coverage $COVERAGE_CS_ATPG

## ELMOS: added variable (optional list) for ATPG limit
set_atpg -abort_limit [lindex $LIMIT_CS_ATPG 0] ; #use first element from list
set ADDITIONAL_LIMITS [lreplace $LIMIT_CS_ATPG 0 0] ; #remove first element from list


report_settings atpg
report_settings simulation
if { $TMAX_DEBUG_MODE } {
   report_settings -all > ${REPORTS_DIR}/${DESIGN_NAME}_stuck_atpg_settings.${tmax_file_ext}.rpt
}

if { $TMAX_OPTIMIZE_PATTERNS } {
   run_atpg -optimize_patterns

   # Optimize patterns runs two-clock ATPG only. Use fast sequential ATPG
   # to generate patterns for logic around memories or other nonscan cells.
   run_atpg fast_sequential_only -auto_compression

   # Additional runs with increased abort limits may improve coverage
   ## ELMOS: added configurable loop for additional runs
   foreach limit $ADDITIONAL_LIMITS {
      set_atpg -abort_limit $limit
      run_atpg fast_sequential_only -auto_compression
   }
   #set_atpg -abort_limit 100
   #run_atpg fast_sequential_only -auto_compression
   #set_atpg -abort_limit 1000
   #run_atpg fast_sequential_only -auto_compression

} else {
   # Standard ATPG run for debug or finding coverage limits.
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
}

## ELMOS: replaced writing by procedure -> "write_results"
### Check simulation results of patterns in debug mode only.
##if { $TMAX_DEBUG_MODE } {
##   run_simulation
##}
##
## write_patterns ${RESULTS_DIR}/${DESIGN_NAME}_stuck.${tmax_file_ext}.bin.gz -format binary -replace -compress gzip
## # If you need patterns in the 1999 version of STIL, instead of the default
## # 2005 version, change to -format stil99 and remove -cellnames type.
## # You may also need to change DRC settings.
## write_patterns ${RESULTS_DIR}/${DESIGN_NAME}_stuck.${tmax_file_ext}.stil.gz -format stil -replace -compress gzip -cellnames type
## #
## # This setting is required to run write_testbench in batch mode:
## setenv LTRAN_SHELL 1
## write_testbench -input ${RESULTS_DIR}/${DESIGN_NAME}_stuck.${tmax_file_ext}.stil.gz -output ${RESULTS_DIR}/${DESIGN_NAME}_stuck.${tmax_file_ext}.maxtb -replace -config_file ${TMAX_SCRIPTS_ROOT}/tmax_maxtb_config.tcl -parameters " -v_file ${NETLIST_FILES} -v_lib ${TMAX_LIBRARY_FILES} -sim_script vcs -log ${RESULTS_DIR}/${DESIGN_NAME}_stuck.${tmax_file_ext}.maxtb.log "
## #
## # This testbench may be used for both parallel and serial simulation.
## # The default is parallel - modify the VCS script to run serial.
## # Simulating all serial patterns may take excessive runtime.
## # To serially simulate only patterns 0 to 10, modify the DEFINES line
## # of the VCS script to read:
## # DEFINES="+define+tmax_serial+tmax_n_pattern_sim=10" 
## #
## write_faults ${RESULTS_DIR}/${DESIGN_NAME}_stuck_post.${tmax_file_ext}.faults.gz -all -replace -compress gzip
## 
## report_patterns -all -types > ${REPORTS_DIR}/${DESIGN_NAME}_stuck_pat_types.${tmax_file_ext}.rpt
## report_summaries faults patterns cpu_usage memory_usage > ${REPORTS_DIR}/${DESIGN_NAME}_stuck_summaries.${tmax_file_ext}.rpt

write_results ${PATTERN_NAME}

# Report for Power-Aware ATPG results
#report_power -per_pattern -percentage > ${REPORTS_DIR}/${DESIGN_NAME}_stuck_power.${tmax_file_ext}.rpt

##################################################################
#    High X-Tolerance Scan Chain Diagnosis:                      #
#    Create a separate pattern set to diagnose scan chain        #
#    failures in high X-tolerant compression mode. If you are    #
#    using compression with default X-tolerance, comment out     #
#    this section because the patterns will be useless.          #
##################################################################

#if { $TMAX_COMPRESSION_MODE } {
#   remove_faults -all
#   set_faults -model stuck -nopersistent_fault_models
#   # Restore default settings for chain test
#   set_atpg -fill random -chain_test 0011R
#   # If power settings were set, uncomment to restore default for shift power
#   #set_atpg -shift_power_effort off
#   set_atpg -xtol_chain_diagnosis high
#   run_atpg -only_chain_diagnosis -auto
#   set_atpg -xtol_chain_diagnosis off
#   set_atpg -patterns [expr [sizeof_collection [get_patterns -all]] + 100]
#   run_atpg -auto
#
#   write_patterns ${RESULTS_DIR}/${DESIGN_NAME}_scdiag.${tmax_file_ext}.bin.gz -format binary -replace -compress gzip
#   # If you need patterns in the 1999 version of STIL, instead of the default
#   # 2005 version, change to -format stil99 and remove -cellnames type.
#   # You may also need to change DRC settings.
#   write_patterns ${RESULTS_DIR}/${DESIGN_NAME}_scdiag.${tmax_file_ext}.stil.gz -format stil -replace -compress gzip -cellnames type
#   #
#   # This setting is required to run write_testbench in batch mode:
#   setenv LTRAN_SHELL 1
#   write_testbench -input ${RESULTS_DIR}/${DESIGN_NAME}_scdiag.${tmax_file_ext}.stil.gz -output ${RESULTS_DIR}/${DESIGN_NAME}_scdiag.${tmax_file_ext}.maxtb -replace -config_file ${TMAX_SCRIPTS_ROOT}/tmax_maxtb_config.tcl -parameters " -v_file ${NETLIST_FILES} -v_lib ${TMAX_LIBRARY_FILES} -sim_script vcs -log ${RESULTS_DIR}/${DESIGN_NAME}_scdiag.${tmax_file_ext}.maxtb.log "
#   #
#   # This testbench may be used for both parallel and serial simulation.
#   # The default is parallel - modify the VCS script to run serial.
#   # Simulating all serial patterns may take excessive runtime.
#   # To serially simulate only patterns 0 to 10, modify the DEFINES line
#   # of the VCS script to read:
#   # DEFINES="+define+tmax_serial+tmax_n_pattern_sim=10" 
#   #
#
#   report_summaries faults patterns cpu_usage memory_usage > ${REPORTS_DIR}/${DESIGN_NAME}_scdiag_summaries.${tmax_file_ext}.rpt
#}

## ELMOS: cell model might cause conflicts with other fault models
read_cell_model -delete

puts "-------------------------------------------------------------------------------"
puts "RM-Info: Completed script [info script]\n"
puts "-------------------------------------------------------------------------------"
