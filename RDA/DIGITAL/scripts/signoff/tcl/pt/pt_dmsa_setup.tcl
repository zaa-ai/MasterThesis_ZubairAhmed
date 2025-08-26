

### pt_setup.tcl file              ###





puts "RM-Info: Running script [info script]\n"
### Start of PrimeTime Runtime Variables ###

##########################################################################################
# PrimeTime Variables PrimeTime Reference Methodology script
# Script: pt_setup.tcl
# Version: O-2019.03-SP2 (July 1, 2019)
# Copyright (C) 2008-2019 Synopsys All rights reserved.
##########################################################################################


######################################
# Report and Results Directories
######################################


set REPORTS_DIR "reports"
set RESULTS_DIR "results"


######################################
# Library and Design Setup
######################################

### Mode : DMSA

# ELMOS: added layout results path and syn/adc as search path and give the usual verilog file
set search_path ". results/ ../layout/results/ ../syn/sdc/ $ADDITIONAL_SEARCH_PATH $search_path"
# Provide list of Verilog netlist files. It can be compressed --- example "A.v B.v C.v"
set NETLIST_FILES               "$DESIGN_NAME.output.v"
# DESIGN_NAME is checked for existence from common_setup.tcl
if {[string length $DESIGN_NAME] > 0} {
} else {
set DESIGN_NAME                   ""  ;#  The name of the top-level design
}





######################################
# DMSA File Section
######################################

set sh_source_uses_search_path true

# ELMOS: source local variable settings file
source -echo user_tcl/dmsa_variables.tcl
# Provide a list of DMSA Corners : best_case, nom, worst_case
#
# The syntax is:
#		1.  set dmsa_corners "corner1 corner2 ..."

#set dmsa_corners      ""

# Provide an array of DMSA Corners Based Libraries : best_case, nom, worst_case
#
# The syntax is dmsa_corner_library_files(corner)
#		1. dmsa_corner_library_files(corner1)
#		2. dmsa_corner_library_files(corner2)

#set dmsa_corner_library_files(corner1) ""
#set dmsa_corner_library_files(corner2) ""


# Provide a list of DMSA modes   : functional, test
#
# The syntax is:
#               1.  set dmsa_modes "mode1 mode2 ..."

#set dmsa_modes      ""

# Provide an array of constraint files
# The syntax will be dmsa_mode_constraint_files(mode)
#		1. dmsa_mode_constraint_files(mode1)
#		2. dmsa_mode_constraint_files(mode2)
#

#set dmsa_mode_constraint_files(mode1) ""
#set dmsa_mode_constraint_files(mode2) ""


#
# Corner-Based Back Annotation Section
#
# The syntax is:
#		1. PARASITIC_FILES(corner1)
#		2. PARASITIC_PATHS(corner1)
#

# The recommended order is to put the block spefs first then the top so that block spefs are read 1st then top
# For example 
# PARASITIC_FILES(slow) "blk1.gpd blk2.gpd ... top.gpd"
# PARASITIC_PATHS(slow) "u_blk1 u_blk2 ... top"
# If you are loading the node coordinates by setting read_parasitics_load_locations true, it is more efficient
# to read the top first so that block coordinates can be transformed as they are read in
# Each PARASITIC_PATH entry corresponds to the related PARASITIC_FILE for the specific block"   
# For toplevel PARASITIC file please use the toplevel design name in PARASITIC_PATHS variable."   
#set PARASITIC_FILES(corner1)	 "" 
#set PARASITIC_PATHS(corner1)	 "" 


# switching activity (VCD/SAIF) file 
set ACTIVITY_FILE ""

# strip_path setting for the activity file
set STRIP_PATH ""

## name map file
set NAME_MAP_FILE ""




######################################
# Setting Number of Hosts and Licenses
######################################
# Set the number of hosts and licenses for compute resource efficient ECO
# Make sure you have sufficient RAM and free disk space in multi_scenario_working_directory
# otherwise it may result in unexpected slowdowns and crashes without proper stack traces
set num_of_scenarios [expr [llength $dmsa_corners] * [llength $dmsa_modes]]
if {$num_of_scenarios < 4} {
	set dmsa_num_of_hosts $num_of_scenarios
} elseif {$num_of_scenarios >= 4 && $num_of_scenarios <= 8} {
	set dmsa_num_of_hosts 4
} else {
	if {[expr ceil([expr $num_of_scenarios/4.0])] > 8} {
		set dmsa_num_of_hosts [expr int(ceil([expr $num_of_scenarios/4.0]))]
	} else {
		set dmsa_num_of_hosts 8
	}
}
set dmsa_num_of_licenses $dmsa_num_of_hosts




######################################
# Fix ECO DRC Setup
######################################
# specify a list of allowable buffers to use for fixing DRC
# Example: set eco_drc_buf_list "BUF4 BUF8 BUF12"
# ELMOS: should be set in dmsa_variables.tcl
#set eco_drc_buf_list ""

######################################
# Fix ECO Timing Setup
######################################
# Specify a list of allowable buffers to use for fixing hold
# Example: set eco_hold_buf_list "DELBUF1 DELBUF2 DELBUF4"
# ELMOS: should be set in dmsa_variables.tcl
#set eco_hold_buf_list ""





######################################
# End
######################################

# ELMOS: additional options for report_(global)_timing and report_constraints
set ADDITIONAL_OPTIONS ""

### End of PrimeTime Runtime Variables ###
puts "RM-Info: Completed script [info script]\n"
