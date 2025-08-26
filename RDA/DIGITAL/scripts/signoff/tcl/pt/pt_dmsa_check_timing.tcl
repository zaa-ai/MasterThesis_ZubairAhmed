puts "RM-Info: Running script [info script]\n"
#################################################################################
# PrimeTime Reference Methodology Script
# Script: dmsa_analysis.tcl
# Version: P-2019.03-SP2 (July 1, 2019)
# Copyright (C) 2009-2019 Synopsys All rights reserved.
#################################################################################


#################################################################################
# 
# This file will produce the reports for the DMSA mode based on the options
# used within the GUI.
#
# The output files will reside within the work/scenario subdirectories.
#
#################################################################################


##################################################################
#    Constraint Analysis Section
##################################################################
remote_execute {
check_constraints -verbose > $REPORTS_DIR/${DESIGN_NAME}_check_constraints.report
}

##################################################################
#    Update_timing and check_timing Section                      #
##################################################################
remote_execute {
set timing_save_pin_arrival_and_slack true
update_timing -full
# Ensure design is properly constrained
check_timing -verbose > $REPORTS_DIR/${DESIGN_NAME}_check_timing.report
}


puts "RM-Info: Completed script [info script]\n"
