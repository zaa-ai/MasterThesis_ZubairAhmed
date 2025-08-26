# #####################################################
# Flow Version 3
# #####################################################
#
# $Date: 2016-11-07 17:44:25 +0100 (Mon, 07 Nov 2016) $
# $Rev: 2394 $:
# $Author: rk $
# #####################################################

##################################################################
# TetraMAX Reference Methodology Diagnosis Example Script        #
# Script: tmax_diagnosis.tcl                                     #
# Version: H-2013.03-SP4 (October 7, 2013)                       #
# Copyright (C) 2010-2013 Synopsys, Inc. All rights reserved.    #
##################################################################

# This script is an example showing typical diagnosis flows.
# It should be customized as needed.

###############################################################
# SETUP: Settings for overall execution                       #
###############################################################

set_messages -log tmax_diagnosis.log -replace
report_version -full

source -echo user_tcl/test_setup.tcl
source -echo $env(PROJECT_HOME)/scripts/test/tcl/tmax/test_global_setup.tcl


if { $TMAX_DEBUG_MODE } {
   set_messages -level expert
}
if { $TMAX_COMPRESSION_MODE } {
   set tmax_file_ext comp
} else {
   set tmax_file_ext scan
}
if { $TMAX_NUM_PROCS > 1 } {
   set_atpg -num_processes $TMAX_NUM_PROCS
   set_simulation -num_processes $TMAX_NUM_PROCS
}
# Parallel diagnostics requires 1 license per process.
# Adjust this if it requires too many licenses.
set TMAX_DIAG_NUM_PROCS $TMAX_NUM_PROCS

##################################################################
# DATAPREP: Prepare data for physical diagnosis                  #
##################################################################


# Physical data preparation is time-consuming so it should be done in advance.
# This step requires LEF and DEF files for the design.
set TMAX_PHYSICAL_DATAPREP FALSE
if { $TMAX_PHYSICAL_DATAPREP } {
   # First, read the image used to generate the pattern being diagnosed:
   read_image ${RESULTS_DIR}/${DESIGN_NAME}_stuck.${tmax_file_ext}.img

   # Read LEF then DEF. The path to the LEF files must be provided.
   # Read the technology LEF (containing the LAYER definitions) first.
   read_physical -format lef <path_to_lef>/<technology>.lef
   read_physical -format lef <path_to_lef>/*.lef
   # The DEF file defaults to the output of the ICC RM.
   read_physical -format def ${RESULTS_DIR}/${DESIGN_NAME}.output.def
   flatten_physical -module ${DESIGN_NAME}

   # If match_names returns M918 warnings, use set_match_names to correct them.
   match_names

   extract_physical -pin_location
   extract_physical -subnets -verbose
   write_physical ${RESULTS_DIR}/${DESIGN_NAME}_diag.${tmax_file_ext}.subnets -subnets -replace
   report_physical -technology > ${REPORTS_DIR}/${DESIGN_NAME}_diag_physical.${tmax_file_ext}.rpt
   report_physical >> ${REPORTS_DIR}/${DESIGN_NAME}_diag_physical.${tmax_file_ext}.rpt
   write_image ${RESULTS_DIR}/${DESIGN_NAME}_diag.${tmax_file_ext}.img -replace -violations -netlist_data -design_view -physical

   # The ydf file is for the interface to Yield Explorer.
   write_ydf ${RESULTS_DIR}/${DESIGN_NAME}_diag_sdf.ydf -all -replace -cell -cell_pin -instance_cell -cell_instance_pin_net -net_path -via_position -net_layer -via

   # Exit when physical data preparation is complete.
   report_summaries cpu_usage memory_usage
   quit
}

##################################################################
# DIAGNOSIS: Run diagnosis for routine failures                  #
##################################################################

# First, read the image used to generate the pattern being diagnosed:
read_image ${RESULTS_DIR}/${DESIGN_NAME}_stuck.${tmax_file_ext}.img
# If LEF and DEF files are available, use composite image:
#read_image ${RESULTS_DIR}/${DESIGN_NAME}_diag.${tmax_file_ext}.img

# Set the pattern file, using the binary pattern set if available:
#set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_trans.${tmax_file_ext}.bin.gz
#set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_trans.${tmax_file_ext}.bin.gz


#set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_stuck.scan.wgl_flat
#set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_stuck.scan.bin
set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_cell_stuck.comp.stil.gz



# Make sure that simulation settings match those used for ATPG.
set_simulation -shift_cycles 1
#set_simulation -timing_exceptions_for_stuck_at
report_settings simulation

# The failure file is required. To understand the diagnosis flow before
# tester data is available, you can generate failure files in TetraMAX.
# These examples show different fault types, but the bracketed information
# must be replaced by design-specific data:
#run_simulation -failure_file datalogs/fail_stuck.log -stuck { 0 <pin_pathname> } -replace
#run_simulation -failure_file datalogs/fail_chain.log -fast { r <chain> <position> } -replace
#run_simulation -subnet [list <n> ] -failure_file datalogs/fail_subnet.log -stuck { 0 <pin_pathname> } -replace
#run_simulation -failure_file datalogs/fail_bridge.log -bridge { adom <pin_pathname1> <pin_pathname2> } -replace

# To diagnose bridging faults, read a bridging node pairs file.
# This can be the same one used for bridging ATPG, or a more complete set.
set_faults -bridge_inputs
read_layout ${NODE_FILE} -likely_pairs
# Failure files from ATE may not be ideal matches for TetraMAX's expectations.
# It is common to have a cycle offset. If so, provide the number to use:
#set_diagnosis -cycle_offset <integer>
# It is common to report only the first several failures. If the reporting
# limit is known, provide it:
#set_diagnosis -failure_memory_limit <integer>
# If the report is limited but the limit is not known, use this setting:
#set_diagnosis -incomplete_failures

# To limit time spent per diagnosis, either because the design is large
# or you are doing volume diagnosis on many parts, there are 2 choices.
#
# You can set a limit to the number of patterns to be simulated:
#set_diagnosis -sample { <failing_patterns> <passing_patterns> }
# Don't use -sample for chain defects.
#
# Or you can set a time limit which requires "set_commands noabort":
#set_diagnosis -time_limit <seconds>
#set_commands noabort

# Report physical subnet IDs to be compatible with Yield Explorer:
set_diagnosis -show physical_subnet_id
set_diagnosis -organization fault
#run_diagnosis datalogs/fail1_cycle.log 
   #> ${REPORTS_DIR}/${DESIGN_NAME}_diagnosis_1.log
   write_ydf ${RESULTS_DIR}/${DESIGN_NAME}_diag_edct.ydf -edct -replace

# Remaining commands are debug examples.
return

set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_cell_stuck.comp.stil.gz
run_diagnosis logs/debug_log/debug_stuck_cell.diag

if {0} {

set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_trans.scan.stil
run_diagnosis datalogs/fail2_trans_cycle.log 


####
set_diagnosis -cycle_offset 1
	set_diagnosis -cycle_offset 0
set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_stuck.scan.stil -split
set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_trans.scan.stil -split
run_diagnosis datalogs/fail1_cycle.log -verbose -display -file datalogs/fail2_trans_cycle.log 

#run_diagnosis datalogs/fail2_trans_cycle.log 


####
set_diagnosis -cycle_offset 1
set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_stuck.scan.stil -split
set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_trans.scan.stil -split
run_diagnosis datalogs/bt75/fail_stuck.log -verbose -display -file datalogs/bt75/fail_trans.log 


set_diagnosis -fault_type all -cycle_offset 1
set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_stuck.scan.stil -split
set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_trans.scan.stil -split
run_diagnosis datalogs/bt75/fail_stuck.log -verbose -display -file datalogs/bt75/fail_trans.log 




set_diagnosis -fault_type transition -cycle_offset 1
set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_trans.scan.stil
run_diagnosis datalogs/bt75/fail_trans.log 


set_diagnosis -fault_type stuck -cycle_offset 1
set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_stuck.scan.stil
run_diagnosis datalogs/bt75/fail_stuck.log 


####
set_diagnosis -fault_type all
set_diagnosis -cycle_offset 1
set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_stuck.scan.stil -split
set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_trans.scan.stil -split
run_diagnosis datalogs/bt56/stuck.log -verbose -display -file datalogs/bt56/trans.log 

set_diagnosis -fault_type stuck -cycle_offset 1
set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_stuck.scan.stil
run_diagnosis datalogs/bt56/stuck.log

set_diagnosis -fault_type transition
set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_trans.scan.stil 
run_diagnosis datalogs/bt56/trans.log


set_diagnosis -fault_type stuck -cycle_offset 1
set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_stuck.scan.stil
run_diagnosis datalogs/bt40/stuck1.log
run_diagnosis datalogs/bt40/stuck2.log
run_diagnosis datalogs/bt40/stuck3.log

run_diagnosis datalogs/bt40/stuck4.log


set_diagnosis -fault_type all  -cycle_offset 1
set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_trans.scan.stil 
run_diagnosis datalogs/bt40/trans.log

	
	
	set_diagnosis -organization class
	set_diagnosis -fault_type all
	set_diagnosis -cycle_offset 0 
	set_diagnosis -delay_type
set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_stuck.scan.stil
run_diagnosis datalogs/bt01/stuck1.log
	run_diagnosis datalogs/bt01/stuck2.log




set_diagnosis -fault_type all  -cycle_offset 1 -intermediate_chain_faults
set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_stuck.scan.stil
run_diagnosis datalogs/btxx/stuck1.log
	
	
	
	####### neu 2021: stuck / trans fail anaylse bei RT:
	
	set_diagnosis -fault_type stuck -cycle_offset 0
	set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_stuck.scan.stil
	run_diagnosis datalogs/b03_stabil/bt03_log_stuck_1.diag
	run_diagnosis datalogs/b03_stabil/bt03_log_stuck_3.diag
	run_diagnosis datalogs/b03_stabil/bt03_log_stuck_5.diag
	
	set_diagnosis -fault_type trans -cycle_offset 0
	set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_trans.scan.stil
	run_diagnosis datalogs/b03_stabil/bt03_log_trans_2.diag
	run_diagnosis datalogs/b03_stabil/bt03_log_trans_4.diag
	run_diagnosis datalogs/b03_stabil/bt03_log_trans_6.diag

}

##################################################################
# DEBUG: Get more information if the results were unexpected     #
##################################################################

# If a chain failure is suspected, but the chain test is missing or passing,
# the most likely chain defects can be found this way:
foreach_in_collection chain [get_scan_chains -all] {
  set chain_name [get_attribute $chain chain_name]
  run_diagnosis fail.log -assume_chain_defect [list all $chain_name ]
}

# If a timing-related defect is suspected but not diagnosed,
# use this setting to increase the priority of delay defects:
set_diagnosis -delay_type
run_diagnosis fail.log

##################################################################
#    End of TetraMAX RM Diagnosis Example script                 #
##################################################################

report_summaries cpu_usage memory_usage
quit
