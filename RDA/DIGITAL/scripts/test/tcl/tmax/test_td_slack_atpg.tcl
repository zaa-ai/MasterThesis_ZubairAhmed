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
check_var COVERAGE_TD_SLACK_ATPG            "100"
check_var LIMIT_TD_SLACK_ATPG               "10"
check_var CUSTOM_TD_SLACK_ADD_FAULTS_SCRIPT ""

##################################################################
#    TD_SLACK_ATPG: Create Patterns for Transition-Delay Test    #
##################################################################
set PATTERN_NAME "trans_slack"

## ELMOS: replaced persistent_fault_model flow by using external pattern
##        and added a variable for the abort limit
## set_faults -model transition
## if { $TMAX_DIRECT_CREDIT } {
##    update_faults -direct_credit
##    report_summaries faults
## }
## set_atpg -abort_limit 10

remove_faults -all
set_faults -model transition

if { [file exists ${GLOBAL_SLACK_FILE}] } {
    ## ELMOS: Detect Slack-Based processing
    ##
    set slackdata_for_atpg     ""
    set slackdata_for_faultsim ""
    redirect -variable delay_settings { report_settings delay }
    regexp {.*slackdata_for_atpg=(yes|no).*} $delay_settings all slackdata_for_atpg
    regexp {.*slackdata_for_faultsim=(yes|no).*} $delay_settings all slackdata_for_faultsim

    ## ELMOS: Enable small delay fault detection
    ##
    set_delay -slackdata_for_atpg
    set_delay -slackdata_for_faultsim    
    set_delay -max_tmgn ${MAX_TMGN}
    set_delay -max_delta_per_fault ${MAX_DELTA_PER_FAULT}
} else {
    puts "RM-Error: Global Slack File not found. Transition Delay Fault testing stopped.\n"
    return
}
    
if {$CUSTOM_TD_SLACK_ADD_FAULTS_SCRIPT != ""} {
    source -echo $CUSTOM_TD_SLACK_ADD_FAULTS_SCRIPT
} else {
    add_faults -all

    ## ELMOS: optimized slack flow to reduce pattern count
    ##
    set slack_report ""
    set max_tmgn     ""

    ## ELMOS: extract value for max_tmgn
    ##
    if { [ eval string last % $MAX_TMGN ] > 0} {
	redirect -variable slack_report { report_faults -slack tmgn 2 }
	regexp {.*The max tmgn for small delay defect faults has been set to (\d+\.\d+).*} $slack_report all max_tmgn
    } else {
	set max_tmgn ${MAX_TMGN} ;# already specified in [ns]
    }
    
    if { ${max_tmgn} == ""} {
	puts "RM-Error: max_tmgn not extracted. Small delay fault list could not be generated. Slack-based ATPG stopped!\n"
	return     
    } else {
	## ELMOS: overwrite delay settings to proceed with 100% of small delay faults
	##        (previous value to be restored after ATPG run)
	set_delay -max_tmgn 100%
		
	## ELMOS: Report all slack faults to find a proper MAX_TMGN
	##
	if { $TMAX_DEBUG_MODE } {
	    report_faults -slack tmgn 50 >> ${REPORTS_DIR}/${DESIGN_NAME}_trans_slack_based_100.${tmax_file_ext}.rpt
	}

	## ELMOS: generate a faultlist with small delay faults only
	##
	report_faults -all -max_tmgn ${max_tmgn} > ${RESULTS_DIR}/${DESIGN_NAME}_${PATTERN_NAME}_post.${tmax_file_ext}.max_tmgn.faults
	remove_faults -all
	puts " The max tmgn to generate the small delay fault list has been set to ${max_tmgn}\n"
	read_faults ${RESULTS_DIR}/${DESIGN_NAME}_${PATTERN_NAME}_post.${tmax_file_ext}.max_tmgn.faults
    }
}

report_summaries faults
read_external_pattern $EXTERNAL_PATTERN_TYPES

## ELMOS: added variable for ATPG coverage
set_atpg -coverage $COVERAGE_TD_SLACK_ATPG

## ELMOS: added variable (optional list) for ATPG limit
set_atpg -abort_limit [lindex $LIMIT_TD_SLACK_ATPG 0] ; #use first element from list
set ADDITIONAL_LIMITS [lreplace $LIMIT_TD_SLACK_ATPG 0 0] ; #remove first element from list

report_settings atpg
report_settings simulation
report_settings delay
if { $TMAX_DEBUG_MODE } {
   report_settings -all > ${REPORTS_DIR}/${DESIGN_NAME}_trans_atpg_settings.${tmax_file_ext}.rpt
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

## ELMOS: replaced faults/pattern writing by common procedure -> "write_results"
### Check simulation results of patterns in debug mode only.
##if { $TMAX_DEBUG_MODE } {
##   run_simulation
##}
##
## write_patterns ${RESULTS_DIR}/${DESIGN_NAME}_trans.${tmax_file_ext}.bin.gz -format binary -replace -compress gzip
## # If you need patterns in the 1999 version of STIL, instead of the default
## # 2005 version, change to -format stil99 and remove -cellnames type.
## # You may also need to change DRC settings.
## write_patterns ${RESULTS_DIR}/${DESIGN_NAME}_trans.${tmax_file_ext}.stil.gz -format stil -replace -compress gzip -cellnames type
## #
## # This setting is required to run write_testbench in batch mode:
## setenv LTRAN_SHELL 1
## write_testbench -input ${RESULTS_DIR}/${DESIGN_NAME}_trans.${tmax_file_ext}.stil.gz -output ${RESULTS_DIR}/${DESIGN_NAME}_trans.${tmax_file_ext}.maxtb -replace -config_file ${TMAX_SCRIPTS_ROOT}/tmax_maxtb_config.tcl -parameters " -v_file ${NETLIST_FILES} -v_lib ${TMAX_LIBRARY_FILES} -sim_script vcs -log ${RESULTS_DIR}/${DESIGN_NAME}_trans.${tmax_file_ext}.maxtb.log "
## #
## # This testbench may be used for both parallel and serial simulation.
## # The default is parallel - modify the VCS script to run serial.
## # Simulating all serial patterns may take excessive runtime.
## # To serially simulate only patterns 0 to 10, modify the DEFINES line
## # of the VCS script to read:
## # DEFINES="+define+tmax_serial+tmax_n_pattern_sim=10" 
## #
## write_faults ${RESULTS_DIR}/${DESIGN_NAME}_trans_post.${tmax_file_ext}.faults.gz -all -replace -compress gzip
## 
## report_patterns -all -types > ${REPORTS_DIR}/${DESIGN_NAME}_trans_pat_types.${tmax_file_ext}.rpt
## report_summaries faults patterns cpu_usage memory_usage > ${REPORTS_DIR}/${DESIGN_NAME}_trans_summaries.${tmax_file_ext}.rpt

write_results ${PATTERN_NAME}

echo "TetraMAX II ATPG can change the clock matrix." >> ${REPORTS_DIR}/${DESIGN_NAME}_trans_clocks.${tmax_file_ext}.rpt
echo "The post-ATPG clock matrix is:" >> ${REPORTS_DIR}/${DESIGN_NAME}_trans_clocks.${tmax_file_ext}.rpt
report_clocks -matrix >> ${REPORTS_DIR}/${DESIGN_NAME}_trans_clocks.${tmax_file_ext}.rpt

if { [file exists ${GLOBAL_SLACK_FILE}] } {
   report_faults -slack effectiveness > ${REPORTS_DIR}/${DESIGN_NAME}_trans_slack_based.${tmax_file_ext}.rpt
   report_faults -slack tmgn 50 >> ${REPORTS_DIR}/${DESIGN_NAME}_trans_slack_based.${tmax_file_ext}.rpt
   report_faults -slack tdet 50 >> ${REPORTS_DIR}/${DESIGN_NAME}_trans_slack_based.${tmax_file_ext}.rpt
   report_faults -slack delta 50 >> ${REPORTS_DIR}/${DESIGN_NAME}_trans_slack_based.${tmax_file_ext}.rpt
}

# Report for Power-Aware ATPG results
#report_power -per_pattern -percentage > ${REPORTS_DIR}/${DESIGN_NAME}_trans_power.${tmax_file_ext}.rpt

## ELMOS: replaced persistent_fault_model flow by using external pattern
## if { !($TMAX_DIRECT_CREDIT) } {
##    set_faults -model bridging
##    run_fault_sim
##    report_summaries faults
## }
## 
## if { !($TMAX_DIRECT_CREDIT) } {
##    set_faults -model stuck
##    run_fault_sim
##    report_summaries faults
## }

## ELMOS: restore previous delay setting 
##
set_delay -max_tmgn ${MAX_TMGN}

if { ${slackdata_for_atpg} == yes } {
    set_delay -slackdata_for_atpg
}
if { ${slackdata_for_faultsim} == yes } {
    set_delay -slackdata_for_faultsim
}

puts "-------------------------------------------------------------------------------"
puts "RM-Info: Completed script [info script]"
puts "-------------------------------------------------------------------------------"
