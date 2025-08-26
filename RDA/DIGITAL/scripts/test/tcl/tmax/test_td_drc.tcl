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
check_var MAX_TMGN                     ""
check_var MAX_DELTA_PER_FAULT          ""
check_var CUSTOM_TD_CONSTRAINTS_SCRIPT ""
check_var PATTERNEXEC                  ""

########################################################################
#    TD_DRC: Run DRC for Transition-Delay and/or Dynamic Bridging Test #
########################################################################
## ELMOS: added here just in case that another DRC has run before
drc -force
remove_atpg_constraints -all
remove_capture_masks -all
remove_cell_constraints -all
remove_clocks -all
remove_compressors -all
remove_pi_constraints -all
remove_po_masks -all
remove_scan_chains -all
remove_scan_enables -all
remove_slow_bidis -all
remove_slow_cells -all

## ELMOS: added here just in case that another DRC has run before
set_atpg -capture_cycles ${CAPTURE_CYCLES}

# These are the most common transition delay settings.
set_delay -launch_cycle system_clock -nopi_changes -common_launch_capture_clock
add_po_masks -all
add_slow_bidis -all

# Set constraints on the Primary Inputs (top-level inputs) here.
# Normally scan enables and resets must be inactive when testing transition delay faults.
# All scan enables and resets must be inactive for Power-Aware ATPG,
# except that resets may pulse if set_atpg -power_effort high is used.
#
# Uncomment with proper port names and off states.
#add_pi_constraints 0 test_se
#add_pi_constraints 1 reset_n
#add_pi_constraints 0 <input_port>

## ELMOS: Set Custom Constraints
if {${CUSTOM_TD_CONSTRAINTS_SCRIPT} != ""} {
    if { [file exists ${CUSTOM_TD_CONSTRAINTS_SCRIPT}] } {
	source -echo ${CUSTOM_TD_CONSTRAINTS_SCRIPT}
    } else {
	puts "RM-Error: Custom Constraint File ${CUSTOM_TD_CONSTRAINTS_SCRIPT} not found.\n"
    }
}

# The timing exceptions flow works best when the set_case_analysis matches the
# TMAX DRC clocking. If this is not the case, change the environment to
# "sdc_case_analysis".
set_sdc -environment tmax_drc
if { $TMAX_DEBUG_MODE } {
   set_sdc -mark_gui_gates -verbose
   foreach sdc_file $EXCEPTION_FILES {
      if { [file exists ${sdc_file}] } {
         read_sdc -echo $sdc_file
      } else {
         puts "RM-Info: SDC file ${sdc_file} was not found. Timing exceptions from other defined SDC files will still be used.\n"
      }
   }
} else {
   foreach sdc_file $EXCEPTION_FILES {
      if { [file exists ${sdc_file}] } {
         read_sdc $sdc_file
      } else {
         puts "RM-Info: SDC file ${sdc_file} was not found. Timing exceptions from other defined SDC files will still be used.\n"
      }
   }
}

# To update waveform timing, uncomment and edit the script as needed:
#source -echo -verbose ${TMAX_SCRIPTS_ROOT}/tmax_update_spf.tcl

report_settings drc
if { $TMAX_DEBUG_MODE } {
   report_settings -all > ${REPORTS_DIR}/${DESIGN_NAME}_trans_drc_settings.${tmax_file_ext}.rpt
}

# The default STIL protocol file is the DC-RM output.
# If you are not using the DC-RM, change the variable in tmax_setup.tcl.

## ELMOS: Generate List of signals not used for DFT
##
set NONDFT_SIGNALS ""
foreach NONDFT_SIGNAL_FILE "$NONDFT_IN_SIGNAL_FILE $NONDFT_OUT_SIGNAL_FILE" {
   if [file exists $NONDFT_SIGNAL_FILE] {
       set fd [open $NONDFT_SIGNAL_FILE r]
       append NONDFT_SIGNALS [read $fd]
       close $fd
   }
}

## ELMOS: Remove unnecessary Signals from ${PROTOCOL_FILE} before running DRC
##
if {$NONDFT_SIGNALS != ""} {
    set fd [open ${PROTOCOL_FILE}.config w ]
    if {$PATTERNEXEC != ""} {
	puts $fd  "INPUT_SPF ${PROTOCOL_FILE} -patternexec ${PATTERNEXEC}"
    } else {
	puts $fd  "INPUT_SPF ${PROTOCOL_FILE}"
    }
    puts $fd  "OUTPUT_SPF ${PROTOCOL_FILE}_o"
    foreach signal $NONDFT_SIGNALS {
       if  {$signal != ""} {
          puts $fd "REMOVE_PORT $signal"
       }
    }
    close $fd
#ELMOS: switched from SYNOPSYS to TMAXSHELL
    exec [getenv {TMAX_SHELL}]/auxx/syn/tmax/spfgen.pl ${PROTOCOL_FILE}.config
    run_drc ${PROTOCOL_FILE}_o
} else {
    if {$PATTERNEXEC != ""} {
	eval run_drc ${PROTOCOL_FILE} -patternexec ${PATTERNEXEC}
    } else {
	run_drc ${PROTOCOL_FILE}
    }
}

# Writing the image file speeds up subsequent ATPG or diagnosis runs.
write_image ${RESULTS_DIR}/${DESIGN_NAME}_trans.${tmax_file_ext}.img -replace -violations -netlist_data -design_view

report_clocks -verbose > ${REPORTS_DIR}/${DESIGN_NAME}_trans_clocks.${tmax_file_ext}.rpt
report_clocks -matrix >> ${REPORTS_DIR}/${DESIGN_NAME}_trans_clocks.${tmax_file_ext}.rpt
report_sdc -all_paths > ${REPORTS_DIR}/${DESIGN_NAME}_trans_exceptions.${tmax_file_ext}.rpt

# These reports are for loadable nonscan cells:
echo "Loadable nonscan cells:" > ${REPORTS_DIR}/${DESIGN_NAME}_trans_nonscan_loading.${tmax_file_ext}.rpt
report_nonscan_cells load >> ${REPORTS_DIR}/${DESIGN_NAME}_trans_nonscan_loading.${tmax_file_ext}.rpt
echo "Non-X loadable nonscan cells:" >> ${REPORTS_DIR}/${DESIGN_NAME}_trans_nonscan_loading.${tmax_file_ext}.rpt
report_nonscan_cells nonx_load >> ${REPORTS_DIR}/${DESIGN_NAME}_trans_nonscan_loading.${tmax_file_ext}.rpt
# This returns an error unless set_simulation -shift_cycles > 0
#analyze_nonscan_loading >> ${REPORTS_DIR}/${DESIGN_NAME}_trans_nonscan_loading.${tmax_file_ext}.rpt

# This report is useful for setting a power budget.
#report_clocks -gating > ${REPORTS_DIR}/${DESIGN_NAME}_trans_clockgating.${tmax_file_ext}.rpt
if { $TMAX_DEBUG_MODE } {
   report_scan_cells -all -verbose > ${REPORTS_DIR}/${DESIGN_NAME}_trans_scan_cells.${tmax_file_ext}.rpt
   report_nonscan_cells -unique > ${REPORTS_DIR}/${DESIGN_NAME}_trans_nonscan_cells.${tmax_file_ext}.rpt
   # Use default report_lockup_latches options starting in N-2017.09-SP1:
   report_lockup_latches -pipeline > ${REPORTS_DIR}/${DESIGN_NAME}_trans_lockup_latches.${tmax_file_ext}.rpt
   if { $TMAX_COMPRESSION_MODE } {
      report_compressors -all -verbose > ${REPORTS_DIR}/${DESIGN_NAME}_trans_compressors.${tmax_file_ext}.rpt
   }
} else {
   ## ELMOS: add report_lockup_latches also when TMAX_DEBUG_MODE is not set
   ##        else tree to not run report lockup latches two times 
   # Use default report_lockup_latches options starting in N-2017.09-SP1:
  report_lockup_latches -pipeline > ${REPORTS_DIR}/${DESIGN_NAME}_trans_lockup_latches.${tmax_file_ext}.rpt
}

# Capture cycles for dynamic testing must be at least 2,
# and should be enough to test through memories.
## ELMOS: added variable for capture_cycle
set_atpg -capture_cycles ${CAPTURE_CYCLES}

set_patterns -histogram_summary

# Settings for Power-Aware ATPG
#
# The power budget should be set based on ATE requirements. Do not set the
# power budget to a number less than the minimum recommended on the last line
# of the report_clocks -gating report.
#set_atpg -power_budget 40
# Uncomment to reduce shift power at the expense of pattern count.
#set_atpg -fill adjacent -shift_power_effort medium
# This chain test pattern allows full diagnostics with minimum power.
#set_atpg -chain_test 001100110011C
# High power effort can reduce test coverage (see the online help).
#set_atpg -power_effort high
if { $TMAX_DEBUG_MODE } {
   set_atpg -verbose
}
# After all ATPG settings are made, write constraints for PrimeTime.
# Use -unit ps if you have used update_scale on the waveform tables.

if { $WFT_TD_DRC != "" } {
   set WFTS ""
   foreach wft $WFT_TD_DRC {
      append WFTS "-wft $wft "
   }
   eval write_timing_constraints ${RESULTS_DIR}/${DESIGN_NAME}_trans_capture.${tmax_file_ext}.tcl -mode capture -replace $WFTS
   write_timing_constraints ${RESULTS_DIR}/${DESIGN_NAME}_trans_shift.${tmax_file_ext}.tcl -mode shift -replace -only_constrain_scanouts
}

# If you are only running TetraMAX to get PrimeTime constraints, quit here.
#quit

## ELMOS: disabled persistent_fault_model flow by using external pattern only.
##        Using external pattern flow it is more flexible to selectively generate
##        pattern with a subset of fault models. Furthermore, with persistent flow 
##        Cell aware pattern cannot be generated with an individual coverage limit.
##
## # Add faults for all fault models to be used for ATPG.
## set_faults -persistent_fault_models
## set_faults -bridge_inputs
## set_faults -model dynamic_bridging
## add_faults -node_file ${NODE_FILE}
## report_summaries faults
## set_faults -model transition
## add_faults -all
## report_summaries faults
## set_faults -bridge_inputs
## set_faults -model bridging
## add_faults -node_file ${NODE_FILE}
## report_summaries faults
## set_faults -model stuck
## add_faults -all
## report_summaries faults

# Use Slack-Based Transition Fault Testing if a global slack file exists.
# The max_tmgn and max_delta_per_fault numbers here are good starting values.
# Change them to design-specific values for later runs.
if { ${GLOBAL_SLACK_FILE} != "" } {
    if { [file exists ${GLOBAL_SLACK_FILE}] } {
	puts "RM-Info: Global Slack File will be used for Transition Delay Fault testing.\n"
	set_faults -model transition
	if { $TMAX_DEBUG_MODE } {
	    # This method is needed to capture all missing slack messages.
	    read_timing ${GLOBAL_SLACK_FILE} -delete -verbose > ${REPORTS_DIR}/${DESIGN_NAME}_trans_m663.${tmax_file_ext}.rpt
	} else {
	    read_timing ${GLOBAL_SLACK_FILE} -delete
	}
	# The starting point for max_tmgn is 30% of the fault list,
	# and for max_delta_per_fault is zero.
	if {${MAX_TMGN} == ""} {
	    set MAX_TMGN "30%" ;# default
	}
	if {${MAX_DELTA_PER_FAULT} == ""} {
	    set MAX_DELTA_PER_FAULT "0";# default
	}
	set_delay -max_tmgn ${MAX_TMGN}
	set_delay -max_delta_per_fault ${MAX_DELTA_PER_FAULT}
    } else {
	## ELMOS: changed to ERROR
	puts "RM-Error: Global Slack File not found. Transition Delay Fault testing will not use slacks.\n"
    }
}

## ELMOS: added more detailed coverage report
set_faults -atpg_effectiveness -fault_coverage

puts "-------------------------------------------------------------------------------"
puts "RM-Info: Completed script [info script]"
puts "-------------------------------------------------------------------------------"
