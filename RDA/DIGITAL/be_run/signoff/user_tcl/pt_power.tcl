#################################################################################
# PrimeTime Reference Methodology Script
# Script: pt.tcl
# Version: H-2013.06 (August 5, 2013)
# Copyright (C) 2008-2013 Synopsys All rights reserved.
################################################################################


# Please do not modify the sdir variable.
# Doing so may cause script to fail.
set sdir "." 

##################################################################
#    Source common and pt_setup.tcl File                         #
##################################################################

source -echo $env(PROJECT_HOME)/scripts/misc/tcl/procs.tcl
source -echo user_tcl/common_setup.tcl
source -echo $env(PROJECT_HOME)/scripts/signoff/tcl/pt/pt_setup.tcl

# make REPORTS_DIR
file mkdir $REPORTS_DIR

# make RESULTS_DIR
file mkdir $RESULTS_DIR 

##################################################################
#    Search Path, Library and Operating Condition Section        #
##################################################################

# Under normal circumstances, when executing a script with source, Tcl
# errors (syntax and semantic) cause the execution of the script to terminate.
# Uncomment the following line to set sh_continue_on_error to true to allow 
# processing to continue when errors occur.
#set sh_continue_on_error true 


set report_default_significant_digits 3 ;
set sh_source_uses_search_path true ;
set search_path ". $search_path" ;

##################################################################
#    Netlist Reading Section                                     #
##################################################################

set CORNER [string tolower $env(CORNER)]

### SET ANALYSIS VARIABLE
set power_enable_analysis true
set power_analysis_mode time_based


set power_default_toggle_rate 0.2
set power_default_static_probability 0.5
set power_default_toggle_rate_reference_clock fastest

read_verilog $NETLIST_FILES
current_design $DESIGN_NAME
link
read_vcd -strip_path snps_sptop/xdut/xdigi ./dig.vcd -time { 733570000 737960000 }

# Build Min/Max Libray Pairs
if {$MIN_LIBRARY_FILES != "" } {
  foreach {max_library min_library} $MIN_LIBRARY_FILES {
    set_min_library $max_library -min_version $min_library
  }
}

#
# Workaround to get PT into bc_wc mode
#
set_operating_conditions -analysis_type single

#
# This requires that each lib has "slow" and "fast" corners specified 
#
set MIN_LIBRARY_NAMES [lsort [get_object_name [filter [get_libs] "@full_name =~ *_FF"]]]
set MAX_LIBRARY_NAMES [lsort [get_object_name [filter [get_libs] "@full_name =~ *_SS"]]]
if {$MIN_LIBRARY_NAMES != "" } {
  foreach max_library $MAX_LIBRARY_NAMES min_library  $MIN_LIBRARY_NAMES {
      puts "Pair slow: $max_library   fast: $min_library"
      set_operating_conditions -max slow -max_library $max_library  -min fast -min_library $min_library
  }
}

##################################################################
#    Back Annotation Section                                     #
##################################################################
#set SPEF_FILE t018lo_1p5m_typical.tluplus_-40.digtop.output.spef.gz
#set SPEF_FILE ${DESIGN_NAME}.${TOOL}.spef.${CORNER}.gz
set SPEF_FILE $env(SPEF_FILE)
 
if { [info exists SPEF_FILE] } {
    read_parasitics -format spef $SPEF_FILE
} else {
    echo "Error: SPEF $SPEF_FILE not found"
}

report_annotated_parasitics 

##################################################################
#    Reading Constraints Section                                 #
##################################################################
source ../syn/sdc/digtop.constraints.procs.tcl
source  $env(SDC_FILE)

set_propagated_clock [all_clocks]
set_clock_uncertainty 0 [all_clocks]

##################################################################
#    Update_timing and check_timing Section                      #
##################################################################

update_timing -full

##################################################################
#    Report Power  Section                                       #
##################################################################
set_power_analysis_options -include all_with_leaf

check_power
update_power

report_power -v > ${REPORTS_DIR}/${DESIGN_NAME}.report_power.${CORNER}.report

if {$env(QUIT) != 0} {
  exit
}






