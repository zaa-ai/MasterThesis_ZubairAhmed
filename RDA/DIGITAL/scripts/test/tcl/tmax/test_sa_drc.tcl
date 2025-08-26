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
check_var CUSTOM_SA_CONSTRAINTS_SCRIPT ""
check_var PATTERNEXEC                  ""

##################################################################
#    SA_DRC: Run DRC for Stuck-At and/or Static Bridging Test    #
##################################################################

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

add_slow_bidis -all

# Set constraints on the Primary Inputs (top-level inputs) here.
# Normally scan enables and resets need no constraints when testing stuck-at faults.
# All scan enables and resets must be inactive for Power-Aware ATPG,
# except that resets may pulse if set_atpg -power_effort high is used.
#
# Uncomment with proper port names and off states.
#add_pi_constraints 0 test_se
#add_pi_constraints 1 reset_n
#add_pi_constraints 0 <input_port>

## ELMOS: Set Custom Constraints
if {${CUSTOM_SA_CONSTRAINTS_SCRIPT} != ""} {
    if { [file exists ${CUSTOM_SA_CONSTRAINTS_SCRIPT}] } {
	source -echo ${CUSTOM_SA_CONSTRAINTS_SCRIPT}
    } else {
	puts "RM-Error: Custom Constraint File ${CUSTOM_SA_CONSTRAINTS_SCRIPT} not found.\n"
    }
}

if {$TMAX2} {
# TetraMAX II simulates the effects of SDC timing exceptions for static
# (stuck-at and/or static bridging) faults in a more useful way than
# TetraMAX ATPG does. Comment this line, and uncomment remove_sdc -all,
# to not use timing exceptions for static faults:
set_simulation -timing_exceptions_for_stuck_at
} else {
# If different exceptions, or a different -hold setting, are used,
# then the old exceptions must be removed before reading new ones.
remove_sdc -all
}

# If SDC timing exceptions were used earlier, they do not need to be read again.
#set_sdc -environment tmax_drc
#if { $TMAX_DEBUG_MODE } {
#   set_sdc -mark_gui_gates -verbose
#   foreach sdc_file $EXCEPTION_FILES {
#      read_sdc -echo $sdc_file
#   }
#} else {
#   foreach sdc_file $EXCEPTION_FILES {
#      read_sdc $sdc_file
#   }
#}

report_settings drc
if { $TMAX_DEBUG_MODE } {
   report_settings -all > ${REPORTS_DIR}/${DESIGN_NAME}_stuck_drc_settings.${tmax_file_ext}.rpt
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
#ELMOS: changed from SYNOPSYS to TMAX_SHELL
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
write_image ${RESULTS_DIR}/${DESIGN_NAME}_stuck.${tmax_file_ext}.img -replace -violations -netlist_data -design_view

report_clocks -verbose > ${REPORTS_DIR}/${DESIGN_NAME}_stuck_clocks.${tmax_file_ext}.rpt
report_clocks -matrix >> ${REPORTS_DIR}/${DESIGN_NAME}_stuck_clocks.${tmax_file_ext}.rpt
report_sdc -all_paths > ${REPORTS_DIR}/${DESIGN_NAME}_stuck_exceptions.${tmax_file_ext}.rpt

# These reports are for loadable nonscan cells:
echo "Loadable nonscan cells:" > ${REPORTS_DIR}/${DESIGN_NAME}_stuck_nonscan_loading.${tmax_file_ext}.rpt
report_nonscan_cells load >> ${REPORTS_DIR}/${DESIGN_NAME}_stuck_nonscan_loading.${tmax_file_ext}.rpt
echo "Non-X loadable nonscan cells:" >> ${REPORTS_DIR}/${DESIGN_NAME}_stuck_nonscan_loading.${tmax_file_ext}.rpt
report_nonscan_cells nonx_load >> ${REPORTS_DIR}/${DESIGN_NAME}_stuck_nonscan_loading.${tmax_file_ext}.rpt
# This returns an error unless set_simulation -shift_cycles > 0
#analyze_nonscan_loading >> ${REPORTS_DIR}/${DESIGN_NAME}_stuck_nonscan_loading.${tmax_file_ext}.rpt

# This report is useful for setting a power budget.
#report_clocks -gating > ${REPORTS_DIR}/${DESIGN_NAME}_stuck_clockgating.${tmax_file_ext}.rpt
if { $TMAX_DEBUG_MODE } {
   report_scan_cells -all -verbose > ${REPORTS_DIR}/${DESIGN_NAME}_stuck_scan_cells.${tmax_file_ext}.rpt
   report_nonscan_cells -unique > ${REPORTS_DIR}/${DESIGN_NAME}_stuck_nonscan_cells.${tmax_file_ext}.rpt
   # Use default report_lockup_latches options starting in N-2017.09-SP1:
   report_lockup_latches -pipeline > ${REPORTS_DIR}/${DESIGN_NAME}_stuck_lockup_latches.${tmax_file_ext}.rpt
   if { $TMAX_COMPRESSION_MODE } {
      report_compressors -all -verbose > ${REPORTS_DIR}/${DESIGN_NAME}_stuck_compressors.${tmax_file_ext}.rpt
   }
} else {
   ## ELMOS: add report_lockup_latches also when TMAX_DEBUG_MODE is not set
   ##		 else tree to not run report lockup latches two times 
   # Use default report_lockup_latches options starting in N-2017.09-SP1:
   report_lockup_latches -pipeline > ${REPORTS_DIR}/${DESIGN_NAME}_stuck_lockup_latches.${tmax_file_ext}.rpt
}

# Capture cycles for static testing should be enough to test through memories.
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
   eval write_timing_constraints ${RESULTS_DIR}/${DESIGN_NAME}_stuck_capture.${tmax_file_ext}.tcl -mode capture -replace $WFTS
   write_timing_constraints ${RESULTS_DIR}/${DESIGN_NAME}_stuck_shift.${tmax_file_ext}.tcl -mode shift -replace -only_constrain_scanouts
}

## ELMOS: added more detailed coverage report
set_faults -atpg_effectiveness -fault_coverage

puts "-------------------------------------------------------------------------------"
puts "RM-Info: Completed script [info script]"
puts "-------------------------------------------------------------------------------"
