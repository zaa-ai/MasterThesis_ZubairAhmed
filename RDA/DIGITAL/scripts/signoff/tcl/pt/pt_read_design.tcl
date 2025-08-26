puts "RM-Info: Running script [info script]\n"
#################################################################################
# PrimeTime Reference Methodology Script
# Script: pt.tcl
# Version: P-2019.03-SP2 (July 1, 2019)
# Copyright (C) 2007-2019 Synopsys All rights reserved.
################################################################################



# Please do not modify the sdir variable.
# Doing so may cause script to fail.
set sdir "." 



##################################################################
#    Source common and pt_setup.tcl File                         #
##################################################################

# ELMOS: moved to main script
# source $sdir/rm_setup/common_setup.tcl
# source $sdir/rm_setup/pt_setup.tcl

# ELMOS: done by makefile
# # make REPORTS_DIR
# file mkdir $REPORTS_DIR

# # make RESULTS_DIR
# file mkdir $RESULTS_DIR 



##################################################################
#    Search Path, Library and Operating Condition Section        #
##################################################################

# Under normal circumstances, when executing a script with source, Tcl
# errors (syntax and semantic) cause the execution of the script to terminate.
# Uncomment the following line to set sh_continue_on_error to true to allow 
# processing to continue when errors occur.
#set sh_continue_on_error true 


set si_enable_analysis true 
set si_xtalk_double_switching_mode clock_network 
  
set power_enable_analysis true 
set power_enable_multi_rail_analysis true 
set power_analysis_mode averaged 

set report_default_significant_digits 3 ;
set sh_source_uses_search_path true ;
set search_path ". $search_path" ;


##################################################################
#    Netlist Reading Section                                     #
##################################################################
set link_path "* $link_path"
read_verilog $NETLIST_FILES

current_design $DESIGN_NAME 
link

puts "RM-Info: Completed script [info script]\n"
