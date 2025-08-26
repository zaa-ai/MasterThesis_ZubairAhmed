puts "-------------------------------------------------------------------------------"
puts "RM-Info: Running script [info script]"
puts "-------------------------------------------------------------------------------"

##################################################################
# TetraMAX Reference Methodology Main Script                     #
# Script: tmax.tcl                                               #
# Version: O-2018.06-SP2 (October 8, 2018)                       #
# Copyright (C) 2008-2018 Synopsys, Inc. All rights reserved.    #
##################################################################


##################################################################
#    BUILD: Read in the design                                   #
##################################################################

# If two definitions of a module are read, last one read is used.
set_netlist -redefined_module last

# If you have modules with no TMAX models, add them to the variable definition in tmax_setup.tcl.
# The -empty_box option may be better if tristate buses are involved.
if { $MODULES_TO_BLACK_BOX != "" } {
   foreach module $MODULES_TO_BLACK_BOX {
      set_build -black_box $module
   }
}
# If you have PLL sources coming from modeled instances, add them to the variable definition in tmax_setup.tcl.
if { $INSTANCES_TO_BLACK_BOX != "" } {
   foreach inst $INSTANCES_TO_BLACK_BOX {
      set_build -instance_modify [list $inst TIEX ]
   }
}

# This variable must be defined in tmax_setup.tcl, as there is no default.
foreach tmax_library $TMAX_LIBRARY_FILES {
   read_netlist $tmax_library -library
}
# The default design netlist is the DC-RM output.
# If you are not using the DC-RM, change the variable in tmax_setup.tcl.
foreach tmax_netlist $NETLIST_FILES {
   read_netlist $tmax_netlist
}

## ELMOS: Remove unnecessary Signals
##
set_build -nodelete_unused_gates ;# keep gates connected to the removed signals that total faults are not reduced

if [file exists $NONDFT_IN_SIGNAL_FILE] {
    set fd [open $NONDFT_IN_SIGNAL_FILE r]
    set nodft [read $fd]
    close $fd
    add_net_connection pi $nodft -remove
}

if [file exists $NONDFT_OUT_SIGNAL_FILE] {
    set fd [open $NONDFT_OUT_SIGNAL_FILE r]
    set nodft [read $fd]
    close $fd
    add_net_connection po $nodft -remove
}


puts "-------------------------------------------------------------------------------"
puts "RM-Info: Completed script [info script]"
puts "-------------------------------------------------------------------------------"
