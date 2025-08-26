puts "-------------------------------------------------------------------------------"
puts "RM-Info: Running script [info script]"
puts "-------------------------------------------------------------------------------"

##################################################################
# ELMOS: check if variable has been defined 
##################################################################
proc check_var {var_name value} {
    global $var_name
    if {![info exists $var_name]} {
	set $var_name $value
    }
}

##################################################################
# ELMOS: Common Procedure to run a fault simulation on 
#        a list of pattern types
##################################################################
proc read_external_pattern {PATTERN_TYPES} {
   global RESULTS_DIR
   global DESIGN_NAME
   global tmax_file_ext

   set_pattern -delete
   if {$PATTERN_TYPES != ""} {
       puts "-------------------------------------------------------------------------------"
       foreach PTYPE $PATTERN_TYPES {
	   puts "RM-Info: Reading external pattern \"${RESULTS_DIR}/${DESIGN_NAME}_${PTYPE}.${tmax_file_ext}.bin.gz\""
	   set_pattern -external ${RESULTS_DIR}/${DESIGN_NAME}_${PTYPE}.${tmax_file_ext}.bin.gz -split_patterns
       }
       puts "-------------------------------------------------------------------------------"
       run_fault_sim
   }
   set_pattern -internal
}

##################################################################
# ELMOS: Common Procedure to write out the generated pattern
#        for a single pattern type
#        (originaly taken from reference methodology)
##################################################################
proc write_pattern_files {PTYPE} {
   global RESULTS_DIR
   global DESIGN_NAME
   global TB_NAME
   global tmax_file_ext
   global NETLIST_FILES
   global TMAX_LIBRARY_FILES
   global TMAX_DEBUG_MODE
   global BIN_OPT
   global WGL_OPT
   global STIL_OPT

   if { $TMAX_DEBUG_MODE } {
      run_simulation
   }

   puts "-------------------------------------------------------------------------------"
   puts "RM-Info: Writing Pattern for \"$PTYPE\""
   puts "-------------------------------------------------------------------------------"

   eval write_patterns ${RESULTS_DIR}/${DESIGN_NAME}_${PTYPE}.${tmax_file_ext}.bin.gz   -format binary   -replace -compress gzip ${BIN_OPT}
   eval write_patterns ${RESULTS_DIR}/${DESIGN_NAME}_${PTYPE}.${tmax_file_ext}.wgl      -format wgl      -replace ${WGL_OPT}
   eval write_patterns ${RESULTS_DIR}/${DESIGN_NAME}_${PTYPE}.${tmax_file_ext}.flat.wgl -format wgl_flat -replace ${WGL_OPT}

   # If you need patterns in the 1999 version of STIL, instead of the default
   # 2005 version, change to -format stil99 and remove -cellnames type.
   # You may also need to change DRC settings.
   eval write_patterns ${RESULTS_DIR}/${DESIGN_NAME}_${PTYPE}.${tmax_file_ext}.stil.gz -format stil -replace -compress gzip -cellnames type ${STIL_OPT}

   # This setting is required to run write_testbench in batch mode:
   setenv LTRAN_SHELL 1

   ## ELMOS: added parameter for testbench name and added "-serial"
   ##        and removed "-config_file ${TMAX_SCRIPTS_ROOT}/tmax_maxtb_config.tcl"

   set TB_MODULE ""
   if {${TB_NAME} != ""} {
       set TB_MODULE "-tb_module ${TB_NAME}"
   }
   set V_LIB     ""
   if {${V_LIB} != ""} {
       set V_LIB "-v_lib ${TMAX_LIBRARY_FILES}"
   }

   write_testbench -input ${RESULTS_DIR}/${DESIGN_NAME}_${PTYPE}.${tmax_file_ext}.stil.gz -output ${RESULTS_DIR}/${DESIGN_NAME}_${PTYPE}.${tmax_file_ext}.maxtb -replace -parameters " -generic_testbench -v_file ${NETLIST_FILES} ${V_LIB} -sim_script vcs -log ${RESULTS_DIR}/${DESIGN_NAME}_${PTYPE}.${tmax_file_ext}.maxtb.log ${TB_MODULE} -serial " 

   # This testbench may be used for both parallel and serial simulation.
   # The default is parallel - modify the VCS script to run serial.
   # Simulating all serial patterns may take excessive runtime.
   # To serially simulate only patterns 0 to 10, modify the DEFINES line
   # of the VCS script to read:
   # DEFINES="+define+tmax_serial+tmax_n_pattern_sim=10" 
   
}

##################################################################
# ELMOS: Common Procedure to write out the all generated results
#        including patterns for a single fault type
##################################################################
proc write_results {PTYPE} {
   global REPORTS_DIR
   global RESULTS_DIR
   global DESIGN_NAME
   global tmax_file_ext
   global EXTERNAL_PATTERN_TYPES
   global JOIN_PATTERN_TYPES
   global HIER_LEVEL
   global MIN_FAULTS

   write_pattern_files ${PTYPE}

   puts "-------------------------------------------------------------------------------"
   puts "RM-Info: Writing Results for \"$PTYPE\""
   puts "-------------------------------------------------------------------------------"
   write_faults ${RESULTS_DIR}/${DESIGN_NAME}_${PTYPE}_post.${tmax_file_ext}.faults.gz -all -replace -compress gzip 
   report_patterns -all -types > ${REPORTS_DIR}/${DESIGN_NAME}_${PTYPE}_pat_types.${tmax_file_ext}.rpt 
   report_summaries faults patterns cpu_usage memory_usage > ${REPORTS_DIR}/${DESIGN_NAME}_${PTYPE}_summaries.${tmax_file_ext}.rpt 

   ## ELMOS: added hierarchical fault report
   ##
   if {${HIER_LEVEL} == ""} {
       set HIER_LEVEL "5" ;# default
   }
   if {${MIN_FAULTS} == ""} {
       set MIN_FAULTS "32";# default
   }
   report_faults -level ${HIER_LEVEL} ${MIN_FAULTS} > ${REPORTS_DIR}/${DESIGN_NAME}_${PTYPE}_faults.${tmax_file_ext}.rpt

   ## ELMOS: keep history of pattern that has been generated
   ##        (used in procedure "read_external_pattern")
   set EXTERNAL_PATTERN_TYPES [lsort -unique [lappend EXTERNAL_PATTERN_TYPES "${PTYPE}"]]
   set JOIN_PATTERN_TYPES [lsort -unique [lappend JOIN_PATTERN_TYPES "${PTYPE}"]]
}

##################################################################
# ELMOS: Common Procedure to join a list of pattern files and
#        to write out into one single pattern file
##################################################################
proc join_pattern_files {PNAME} {
   global RESULTS_DIR
   global DESIGN_NAME
   global tmax_file_ext
   global JOIN_PATTERN_TYPES
   global TMAX_DEBUG_MODE

   set_pattern -delete
   if {$JOIN_PATTERN_TYPES != ""} {
       puts "-------------------------------------------------------------------------------"
       foreach PTYPE $JOIN_PATTERN_TYPES {
	   puts "RM-Info: Reading external pattern \"${RESULTS_DIR}/${DESIGN_NAME}_${PTYPE}.${tmax_file_ext}.bin.gz\""
	   set_pattern -external ${RESULTS_DIR}/${DESIGN_NAME}_${PTYPE}.${tmax_file_ext}.bin.gz -append
       }
       puts "-------------------------------------------------------------------------------"
   }

   if { $TMAX_DEBUG_MODE } {
      run_simulation
   }

   write_pattern_files ${PNAME}

   ## clear history of pattern that has been written out
   ## 
   set JOIN_PATTERN_TYPES ""
}

##################################################################
# TetraMAX Reference Methodology Main Script                     #
# Script: tmax.tcl                                               #
# Version: O-2018.06-SP2 (October 8, 2018)                       #
# Copyright (C) 2008-2018 Synopsys, Inc. All rights reserved.    #
##################################################################

# Option Name:  Setting
# =====================
# ATPG Engine:  TETRAMAX/TETRAMAX_II
# Transition Delay:  TRUE
# Stuck-at Testing:  TRUE
# Dynamic Bridging:  TRUE
# Static Bridging:  TRUE
# Path Delay:  FALSE
# Power-Aware ATPG:  FALSE
# On-Chip Clocking:  FALSE
# DFTMAX Ultra Compression:  FALSE
# Protocol Creation:  FALSE
# Lynx-Compatible:  FALSE

##################################################################
#    SETUP: Settings for overall execution                       #
##################################################################

## ELMOS: initialize variables if not defined
##        
check_var EXTERNAL_PATTERN_TYPES "" ;# global variable definition ---> DO NOT MODIFY!!! <---
check_var JOIN_PATTERN_TYPES     "" ;# global variable definition ---> DO NOT MODIFY!!! <---
check_var WGL_OPT                ""
check_var BIN_OPT                ""
check_var STIL_OPT               ""
check_var HIER_LEVEL             ""
check_var MIN_FAULTS             ""

# Log file name is hard-coded to capture setup values. Change the name if desired.
## ELMOS
set_messages -log logs/tmax/tmax.log -replace
report_version -full

## ELMOS: original tmax_setup.tcl is now partly included within common_setup.tcl
##        or directly moved into this script
# set TMAX_SETUP_ROOT "./rm_setup"
# source -echo ${TMAX_SETUP_ROOT}/tmax_setup.tcl

##################################################################
#    RUNTIME: Set runtime variables                              #
##################################################################

## ELMOS: Detect tmax1 or tmax2
##        Required to diffentiate some options between tmax1 and tmx2

redirect -variable atpg_settings { report_settings atpg }
regexp {.*num_threads=([0-9]+).*} $atpg_settings all default_num_threads

if { $default_num_threads > 0 } {
    set TMAX2 TRUE
} else {
    set TMAX2 FALSE
}

## ELMOS: Dependent on using tmax1 or tmax2
##        -> tmax1: multiprocs
##        -> tmax2: multithreads (optimized pattern not supported)
##
## # Set the number of threads to be used for ATPG and simulation.
## # If no value is set, the default is 8.
## 
## # Set TMAX_NUM_PROCS to > 1 for multicore ATPG and simulation.
## # Make sure that your compute farm settings allow multicore processing.
## 
## # Set TMAX_OPTIMIZE_PATTERNS to TRUE for the final ATPG run to optimize
## # pattern count at the expense of runtime. This optimization applies to
## # the stuck-at and transition delay fault models; other fault models may
## # not get better results so they are not supported in the RM.

if {$TMAX2} {
    set TMAX2_NUM_THREADS 8
    set TMAX_NUM_PROCS    1
    set TMAX_OPTIMIZE_PATTERNS FALSE
} else {
    set TMAX2_NUM_THREADS 0
    set TMAX_NUM_PROCS    4
    set TMAX_OPTIMIZE_PATTERNS TRUE
}

## ELMOS: Not required because of disabled persistent fault model flow
## # Change TMAX_DIRECT_CREDIT to FALSE to fault simulate patterns for multiple
## # fault model flow. Fault simulation takes much more time but can result in
## # smaller overall pattern sets.
## set TMAX_DIRECT_CREDIT FALSE


if { $TMAX_DEBUG_MODE } {
   set_messages -level expert
}
if { $TMAX_COMPRESSION_MODE } {
   set tmax_file_ext comp
} else {
   set tmax_file_ext scan
}

set_atpg -num_threads $TMAX2_NUM_THREADS
set_simulation -num_threads $TMAX2_NUM_THREADS
if { $TMAX_NUM_PROCS > 1 } {
   set_atpg -num_processes $TMAX_NUM_PROCS
   set_simulation -num_processes $TMAX_NUM_PROCS
}
# Source tmax2pt.tcl which will be used later.
#ELMOS: switchted from SYNOPSYS to TMAX_SHELL
source $env(TMAX_SHELL)/auxx/syn/tmax/tmax2pt.tcl

# Uncomment if you want the run to continue if errors are encountered.
#set_commands noabort

## ELMOS
if { !($TMAX_DEBUG_MODE) } {
   set_commands exit
}

# If you have rules to downgrade (with or without masking),
# add them to the variable definitions in tmax_setup.tcl.
if { $RULES_TO_DOWNGRADE != "" } {
   foreach tmax_rule $RULES_TO_DOWNGRADE {
      set_rules $tmax_rule warning
      report_rules $tmax_rule
   }
}
if { $RULES_TO_MASK != "" } {
   foreach tmax_rule $RULES_TO_MASK {
      set_rules $tmax_rule warning -mask
      report_rules $tmax_rule
   }
}

##################################################################
#    Define global variables for both DRC runs                   #
##################################################################

# This setting allows better analysis of detected-by-implication faults.
set_drc -extract_cascaded_clock_gating

# This setting can reduce the runtime required for parallel Verilog
# simulation of the patterns, but using it reduces test coverage.
#set_drc -noshadows

# These settings allow ATPG to use nonscan cell values loaded by the last shift.
# Fault simulation can use more shifts, but ATPG can only use 1 shift,
# and write_timing_constraints can only write checks for 1 shift.
set_drc -load_nonscan_cells
set_simulation -shift_cycles 1

# If there are Z1 violations when loadable nonscan cells are used,
# this may be needed to resolve them:
#set_drc -deterministic_z1check

# Use this setting if there are internally-generated asynchronous resets.
#set_drc -allow_unstable_set_resets

# This additional setting is needed if M404 warnings are printed when
# using write_patterns -format stil99 (not with -format stil).
#set_drc -nodslave_remodel -noreclassify_invalid_dslaves

# ATPG pattern resimulation should not be used in the current release of TetraMAX II.
#set_atpg -resim_atpg_patterns fault_sim

# Use this setting to prevent multiload patterns, which increase coverage
# but are expensive in terms of test time and test data volume.
#set_atpg -single_load_per_pattern

# This setting prevents pipeline scan data registers from capturing known
# values during capture cycles, which can cause parallel-load simulation
# mismatches.
set_simulation -nopipeline_cells

if { $TMAX_DEBUG_MODE } {
   set_drc -store_setup
   set_simulation -progress_message 10
   if { $TMAX_COMPRESSION_MODE } {
      set_drc -compressor_debug_data
   }
}

# These settings allow more flexible use of fault lists.
set_faults -summary verbose -noequiv_code
# These settings give pessimistic reports, but the information can be useful.
#set_faults -fault_coverage -pt_credit 0

puts "-------------------------------------------------------------------------------"
puts "RM-Info: Completed script [info script]"
puts "-------------------------------------------------------------------------------"
