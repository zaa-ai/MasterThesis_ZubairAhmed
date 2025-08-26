puts "RM-Info: Running script [info script]\n"

#################################################################################
# PrimeTime Reference Methodology Script
# Script: dmsa_mc.tcl
# Version: P-2019.03-SP2 (July 1, 2019)
# Copyright (C) 2009-2019 Synopsys All rights reserved.
#################################################################################

set sh_source_uses_search_path true
set report_default_significant_digits 3

# make REPORTS_DIR
file mkdir $REPORTS_DIR

# make RESULTS_DIR
file mkdir $RESULTS_DIR 

# Under normal circumstances, when executing a script with source, Tcl
# errors (syntax and semantic) cause the execution of the script to terminate.
# Uncomment the following line to set sh_continue_on_error to true to allow
# processing to continue when errors occur.
#set sh_continue_on_error true

set si_enable_analysis true 
set si_xtalk_double_switching_mode clock_network 
set timing_remove_clock_reconvergence_pessimism true 

set power_enable_analysis true 
set power_enable_multi_rail_analysis true 
set power_analysis_mode averaged 


echo "Checking $dmsa_corner_library_files($corner)"

set select_dmsa_corner_libs "";

foreach dml $dmsa_corner_library_files($corner)  {
    lappend select_dmsa_corner_libs $dml
}

echo "select_dmsa_corner_libs $select_dmsa_corner_libs"

set link_path "* $select_dmsa_corner_libs"
read_verilog $NETLIST_FILES
current_design $DESIGN_NAME
link


##################################################################
#    Back Annotation Section                                     #
##################################################################

if { [info exists PARASITIC_PATHS] && [info exists PARASITIC_FILES] } {
foreach para_path $PARASITIC_PATHS($corner) para_file $PARASITIC_FILES($corner) {
   if {[string compare $para_path $DESIGN_NAME] == 0} {
      read_parasitics -keep_capacitive_coupling $para_file 
   } else {
      read_parasitics -path $para_path -keep_capacitive_coupling $para_file 
   }
}
}



######################################
# reading design constraints
######################################

# ELMOS: added corner specific constraint file
if {[info exists dmsa_mode_constraint_files(${mode}_${corner})]} {
        foreach dmcf $dmsa_mode_constraint_files(${mode}_${corner}) {
                if {[file extension $dmcf] eq ".sdc"} {
                        read_sdc -echo $dmcf
                } else {
                        source -echo $dmcf
                }
        }
}







##################################################################  
#    Power Switching Activity: Vector Free Flow                  #  
##################################################################  
set power_default_toggle_rate 0.1 			
set power_default_static_probability 0.5 		
report_switching_activity -list_not_annotated           





puts "RM-Info: Completed script [info script]\n"
