puts "RM-Info: Running script [info script]\n"
#################################################################################
# PrimeTime Reference Methodology Script
# Script: pt.tcl
# Version: P-2019.03-SP2 (July 1, 2019)
# Copyright (C) 2007-2019 Synopsys All rights reserved.
################################################################################



##################################################################
#    Setting Derate and CRPR Section                             #
##################################################################



set timing_remove_clock_reconvergence_pessimism true 


##################################################################
#    Fix ECO Variable Setup                                      #
##################################################################
set timing_save_pin_arrival_and_slack true

puts "RM-Info: Completed script [info script]\n"
