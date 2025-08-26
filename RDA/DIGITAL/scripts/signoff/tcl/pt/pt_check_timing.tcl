puts "RM-Info: Running script [info script]\n"
#################################################################################
# PrimeTime Reference Methodology Script
# Script: pt.tcl
# Version: P-2019.03-SP2 (July 1, 2019)
# Copyright (C) 2007-2019 Synopsys All rights reserved.
################################################################################


##################################################################
#    Constraint Analysis Section
##################################################################
check_constraints -verbose > $REPORTS_DIR/${DESIGN_NAME}_${SCENARIO}_check_constraints.report

##################################################################
#    Update_timing and check_timing Section                      #
##################################################################

update_timing -full
check_timing -verbose > $REPORTS_DIR/${DESIGN_NAME}_${SCENARIO}_check_timing.report

puts "RM-Info: Completed script [info script]\n"
