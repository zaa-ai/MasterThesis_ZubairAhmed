##########################################################################################
# Version: S-2021.06
# Copyright (C) 2014-2021 Synopsys, Inc. All rights reserved.
##########################################################################################


# ELMOS: appended scripts path; added user_tcl as highest priority
set search_path [list user_tcl $env(PROJECT_HOME)/scripts/layout/tcl/icc2/rm_setup $env(PROJECT_HOME)/scripts/layout/tcl/icc2/rm_icc2_pnr_scripts ./rm_tech_scripts ./rm_user_plugin_scripts]
lappend search_path .

if {$synopsys_program_name == "icc2_shell"} {
   set_host_options -max_cores $SET_HOST_OPTIONS_MAX_CORE

   ## The default number of significant digits used to display values in reports
   set_app_options -name shell.common.report_default_significant_digits -value 3 ;# tool default is 2

   ## Enable on-disk operation for copy_block to save block to disk right away
   #  set_app_options -name design.on_disk_operation -value true ;# default false and global-scoped
}

set sh_continue_on_error true

if {![file exists $OUTPUTS_DIR]} {file mkdir $OUTPUTS_DIR} ;# do not change this line or directory may not be created properly
if {![file exists $REPORTS_DIR]} {file mkdir $REPORTS_DIR} ;# do not change this line or directory may not be created properly
if {$WRITE_QOR_DATA && ![file exists $WRITE_QOR_DATA_DIR]} {file mkdir $WRITE_QOR_DATA_DIR} ;# do not change this line or directory may not be created properly
if {$WRITE_QOR_DATA && ![file exists $COMPARE_QOR_DATA_DIR]} {file mkdir $COMPARE_QOR_DATA_DIR} ;# do not change this line or directory may not be created properly

########################################################################################## 
## Message handling
##########################################################################################
suppress_message ATTR-11 ;# suppress the information about that design specific attribute values override over library values
## set_message_info -id ATTR-11 -limit 1 ;# limit the message normally printed during report_lib_cells to just 1 occurence
set_message_info -id PVT-012 -limit 1
set_message_info -id PVT-013 -limit 1
puts "RM-info: Hostname: [sh hostname]"; puts "RM-info: Date: [date]"; puts "RM-info: PID: [pid]"; puts "RM-info: PWD: [pwd]"

