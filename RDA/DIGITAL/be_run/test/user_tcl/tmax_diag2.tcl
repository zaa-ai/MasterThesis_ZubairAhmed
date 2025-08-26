
## SETUP
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
# DIAGNOSIS: Run diagnosis for routine failures                  #
##################################################################

# First, read the image used to generate the pattern being diagnosed:
read_image ${RESULTS_DIR}/${DESIGN_NAME}_stuck.${tmax_file_ext}.img

#STUCK
#read_image ${RESULTS_DIR}/${DESIGN_NAME}_stuck.${tmax_file_ext}.img

# Make sure that simulation settings match those used for ATPG.
set_simulation -shift_cycles 1 
#set_simulation -timing_exceptions_for_stuck_at
report_settings simulation

# To diagnose bridging faults, read a bridging node pairs file.
# This can be the same one used for bridging ATPG, or a more complete set.
#set_faults -bridge_inputs
#read_layout ${NODE_FILE} -likely_pairs
# Failure files from ATE may not be ideal matches for TetraMAX's expectations.

set_diagnosis -show physical_subnet_id
set_diagnosis -organization fault
#run_diagnosis datalogs/fail1_cycle.log 
   #> ${REPORTS_DIR}/${DESIGN_NAME}_diagnosis_1.log

return
### DO ANALYSIS


##################################################################
proc diag_stuck fail_log {
	global RESULTS_DIR
	global DESIGN_NAME
    set_diagnosis -fault_type stuck -cycle_offset 0
    set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_cell_stuck.comp.stil.gz
    run_diagnosis $fail_log
}

##################################################################
proc diag_trans fail_log {
	global RESULTS_DIR
	global DESIGN_NAME	
    set_diagnosis -fault_type trans -cycle_offset 0
    set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_trans.scan.stil
    run_diagnosis $fail_log
}


##################################################################
## find the FFs which catched the failures
proc diag_stuck_only_ff fail_log {
    global RESULTS_DIR;    global DESIGN_NAME
    #set fail_log "datalogs/b03_stabil/bt03_log_stuck_1.diag"
    set_diagnosis -fault_type stuck -cycle_offset 0
    set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_cell_stuck.comp.stil.gz
    redirect -variable text {run_diagnosis $fail_log -only_report_failures}
    set pattern {\s*\d+\s+(C\d)\s+(\d+)\s+\d+}
	
## list at end of comand suppress the long output
    set matchTuples [regexp -all -inline $pattern $text]; list
    set first 1
    foreach {whole CHAIN CELL} $matchTuples {
       redirect -variable text {report_scan_cells [list $CHAIN  $CELL]}
       if {$first == 1} {
	    puts $text
	    set first 0   
       } else {
	    puts [lindex [regexp -all -inline -line -- {^.*MASTER.*$} $text] 0 ] 
       }
    }
}


return


diag_stuck_only_ff maxrun/digtop_cell_stuck.comp.maxtb.diag


##########################################################################
#set_diagnosis -fault_type all  -cycle_offset 1 -intermediate_chain_faults
#set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_stuck.scan.stil
#run_diagnosis datalogs/btxx/stuck1.log

#STUCK
set_diagnosis -fault_type stuck -cycle_offset 0
set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_stuck.scan.stil
run_diagnosis datalogs/b03_stabil/bt03_log_stuck_1.diag
	
#TRANS
set_diagnosis -fault_type trans -cycle_offset 0
set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_trans.scan.stil
run_diagnosis datalogs/b03_stabil/bt03_log_trans_2.diag

#ALL
set_diagnosis -fault_type all -cycle_offset 0
set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_trans.scan.stil
run_diagnosis datalogs/b03_stabil/bt03_log_trans_2.diag

#BT02
set_diagnosis -fault_type stuck -cycle_offset 0
set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_stuck.scan.stil
run_diagnosis datalogs/bt02_03_stuck_rt/bt02_stuck_1.diag 
run_diagnosis datalogs/bt02_03_stuck_rt/bt02_stuck_1.diag -assume_chain_defect stuck C1
#CHAINS: assume a failure on FFs
foreach_in_collection chain [get_scan_chains -all] {
  set chain_name [get_attribute $chain chain_name]
  run_diagnosis datalogs/bt02_03_stuck_rt/bt02_stuck_1.diag -assume_chain_defect [list all $chain_name ]
}




set_diagnosis -fault_type stuck -cycle_offset 0
set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_stuck.scan.stil
run_diagnosis datalogs/bt40/stuck1.log
run_diagnosis datalogs/bt40/stuck2.log
run_diagnosis datalogs/bt40/stuck3.log

run_diagnosis datalogs/bt40/stuck4.log
##################################################################
# DEBUG: Get more information if the results were unexpected     #
##################################################################
#CHAINS: assume a failure on FFs
set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_stuck.scan.stil
set_diagnosis -fault_type stuck -cycle_offset 0
foreach_in_collection chain [get_scan_chains -all] {
  set chain_name [get_attribute $chain chain_name]
  run_diagnosis datalogs/bt40/stuck1.log -assume_chain_defect [list all $chain_name ]
	run_diagnosis datalogs/bt40/stuck2.log -assume_chain_defect [list all $chain_name ]
	run_diagnosis datalogs/bt40/stuck3.log -assume_chain_defect [list all $chain_name ]
	run_diagnosis datalogs/bt40/stuck4.log -assume_chain_defect [list all $chain_name ]

	
}

#CHAINS: assume a failure on FFs
set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_stuck.scan.stil
set_diagnosis -fault_type stuck -cycle_offset 0
foreach_in_collection chain [get_scan_chains -all] {
  set chain_name [get_attribute $chain chain_name]
  run_diagnosis datalogs/bt56/stuck.log -assume_chain_defect [list all $chain_name ]
  }
#CHAINS: assume a failure on FFs
set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_stuck.scan.stil
set_diagnosis -fault_type stuck -cycle_offset 0
foreach_in_collection chain [get_scan_chains -all] {
  set chain_name [get_attribute $chain chain_name]
  run_diagnosis datalogs/bt75/fail_stuck.log -assume_chain_defect [list all $chain_name ]
    }



##################################################################
# DEBUG: Get more information if the results were unexpected     #
##################################################################
#CHAINS: assume a failure on FFs
set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_stuck.scan.stil
set_diagnosis -fault_type stuck -cycle_offset 0
foreach_in_collection chain [get_scan_chains -all] {
  set chain_name [get_attribute $chain chain_name]
  run_diagnosis datalogs/b03_stabil/bt03_log_stuck_1.diag -assume_chain_defect [list all $chain_name ]
}


######################################################################
# DEBUG2: TIMING Get more information if the results were unexpected #
######################################################################
set_patterns -external ${RESULTS_DIR}/${DESIGN_NAME}_stuck.scan.stil
set_diagnosis -delay_type
run_diagnosis datalogs/b03_stabil/bt03_log_stuck_1.diag

