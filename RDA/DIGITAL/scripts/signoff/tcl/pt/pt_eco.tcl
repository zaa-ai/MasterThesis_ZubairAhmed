puts "RM-Info: Running script [info script]\n"
#################################################################################
# PrimeTime Reference Methodology Script
# Script: pt.tcl
# Version: P-2019.03-SP2 (July 1, 2019)
# Copyright (C) 2007-2019 Synopsys All rights reserved.
################################################################################


##################################################################
#    Fix ECO Power Cell Downsize Section                         #
##################################################################
# Note if power attributes flow is desired fix_eco_power -power_attribute
# then attribute file needs to be provided for lib cells.
# See 2014.12 update training for examples
#
# PBA mode can be enabled by changing the -pba_mode option
# See fix_eco_power man page for more details on PBA based fixing
# Additional PBA controls are also available with -pba_path_selection_options
# Reporting options should be changed to reflect PBA based ECO
#
fix_eco_power -pba_mode none -verbose

##################################################################
#    Fix ECO Power Buffer Removal                                #
##################################################################
# Power recovery also has buffer removal capability.  
# Buffer removal usage is as follows:
# fix_eco_power -method remove_buffer
# When can specify -method remove_buffer, it cannot be used in conjunction 
# with size_cell, so buffer removal needs to be done in a separate 
# fix_eco_power command.  Please see the man page for additional details.




#power attribute hold fixing
#Below are the required options for power attribute hold fixing
#fix_eco_timing -type hold -power_attribute <attr name>
#leakage based hold fixing
#Below are the required options for leakage based hold fixing
#fix_eco_timing -type hold -power_mode leakage

puts "RM-Info: Completed script [info script]\n"
