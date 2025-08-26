puts "RM-Info: Running script [info script]\n"
#################################################################################
# PrimeTime Reference Methodology Script
# Script: pt.tcl
# Version: P-2019.03-SP2 (July 1, 2019)
# Copyright (C) 2007-2019 Synopsys All rights reserved.
################################################################################


##################################################################
#    Back Annotation Section                                     #
##################################################################
if { [info exists PARASITIC_PATHS] && [info exists PARASITIC_FILES] } {
foreach para_path $PARASITIC_PATHS para_file $PARASITIC_FILES {
   if {[string compare $para_path $DESIGN_NAME] == 0} {
      read_parasitics -keep_capacitive_coupling $para_file 
   } else {
      read_parasitics -path $para_path -keep_capacitive_coupling $para_file 
   }
}
}



##################################################################
#    Reading Constraints Section                                 #
##################################################################
if  {[info exists CONSTRAINT_FILES]} {
        foreach constraint_file $CONSTRAINT_FILES {
                if {[file extension $constraint_file] eq ".sdc"} {
                        read_sdc -echo $constraint_file
                } else {
                        source -echo $constraint_file
                }
        }
}

puts "RM-Info: Completed script [info script]\n"
