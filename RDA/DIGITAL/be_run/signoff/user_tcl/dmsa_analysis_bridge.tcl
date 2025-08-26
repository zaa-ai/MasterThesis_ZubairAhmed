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
check_constraints -verbose > $REPORTS_DIR/${DESIGN_NAME}_check_bridge_constraints.report
}

##################################################################
#    Update_timing and check_timing Section                      #
##################################################################
remote_execute {
set timing_save_pin_arrival_and_slack true
update_timing -full
# Ensure design is properly constrained
check_timing -verbose > $REPORTS_DIR/${DESIGN_NAME}_check_bridge_timing.report
}


##################################################################
#   Writing an Reduced Resource ECO design                       #
##################################################################
# PrimeTime has the capability to write out an ECO design which 
# is a smaller version of the orginal design ECO can be performed
# with fewer compute resources.
#
# Writes an ECO design  that  preserves  the  specified  violation
# types  compared to those in the original design. You can specify
#  one or more of the following violation types:
#              o setup - Preserves setup timing results.
#              o hold - Preserves hold timing results.
#              o max_transistion - Preserves max_transition results.
#              o max_capacitance - Preserves max_capacitance results.
#              o max_fanout - Preserves max_fanout results.
#              o noise - Preserves noise results.
#              o timing - Preserves setup and hold timing results.
#              o drc  -  Preserves  max_transition,  max_capacitance,  
#                and max fanout results.
# There is also capability to write out specific endpoints with
# the -endpoints options.
#
# In DMSA analyis the RRECO design is written out relative to all
# scenarios enabled for analysis.
# 
# To create a RRECO design the user should perform the following 
# command and include violations types which the user is interested
# in fixing, for example for setup and hold.
# 
# write_eco_design  -type {setup hold} my_RRECO_design
#
# Once the RRECO design is created, the user then would invoke 
# PrimeTIme ECO in a seperate session and access the appropriate
# resourses and then read in the RRECO to perform the ECO
# 
# set_host_options ....
# start_hosts
# read_eco_design my_RRECO_design
# fix_eco...
#
# For more details please see man pages for write_eco_design
# and read_eco design.


##################################################################
#    Report_timing Section                                       #
##################################################################
#==============================================================================
#Cover through reporting from 2018.06* version
#get_timing_paths and report_timing commands are enhanced with a new option, -cover_through through_list, which collects the single worst violating path through    each of the objects specified in a list. 
#For example,
#pt_shell> remote_execute {get_timing_paths -cover_through {n1 n2 n3} }
#This command creates a collection containing the worst path through n1, the worst path
#through n2, and the worst path through n3, resulting in a collection of up to three paths.
#=======================================================================
report_global_timing -pba_mode exhaustive > $REPORTS_DIR/${DESIGN_NAME}_dmsa_report_bridge_global_timing.report
report_timing -crosstalk_delta -slack_lesser_than 0.0 -pba_mode exhaustive -delay min_max -nosplit -input -net -sign 4 > $REPORTS_DIR/${DESIGN_NAME}_dmsa_report_timing.report

report_analysis_coverage -status_details {untested} -nosplit > $REPORTS_DIR/${DESIGN_NAME}_dmsa_report_bridge_analysis_coverage.report 

remote_execute {
report_clock -skew -attribute > $REPORTS_DIR/${DESIGN_NAME}_report_bridgel_clock.report 
# Clock Network Double Switching Report
report_si_double_switching -nosplit -rise -fall > $REPORTS_DIR/${DESIGN_NAME}_report_bridge_si_double_switching.report
}
report_constraints -pba_mode exhaustive -all_violators -verbose > $REPORTS_DIR/${DESIGN_NAME}_dmsa_report_bridge_constraints.report
remote_execute {
report_constraints -pba_mode exhaustive -all_violators -verbose > $REPORTS_DIR/${DESIGN_NAME}_report_bridge_constraints.report
report_design > $REPORTS_DIR/${DESIGN_NAME}_report_bridge_design.report
report_net > $REPORTS_DIR/${DESIGN_NAME}_report_bridge_net.report
}

# Noise Settings
remote_execute {
set_noise_parameters -enable_propagation -analysis_mode report_at_endpoint
check_noise > $REPORTS_DIR/${DESIGN_NAME}_check_bridge_noise.report
update_noise

# Noise Reporting
report_noise -nosplit -all_violators -above -low > $REPORTS_DIR/${DESIGN_NAME}_report_bridge_noise_all_viol_abv_low.report
report_noise -nosplit -nworst 10 -above -low > $REPORTS_DIR/${DESIGN_NAME}_report_bridge_noise_alow.report

report_noise -nosplit -all_violators -below -high > $REPORTS_DIR/${DESIGN_NAME}_report_bridge_noise_all_viol_below_high.report
report_noise -nosplit -nworst 10 -below -high > $REPORTS_DIR/${DESIGN_NAME}_report_bridge_noise_below_high.report

}

# Merged Noise Reporting
report_noise -nosplit -all_violators -above -low > $REPORTS_DIR/${DESIGN_NAME}_dmsa_report_bridge_noise_all_viol_abv_low.report
report_noise -nosplit -nworst 10 -above -low > $REPORTS_DIR/${DESIGN_NAME}_dmsa_report_bridge_noise_alow.report

report_noise -nosplit -all_violators -below -high > $REPORTS_DIR/${DESIGN_NAME}_dmsa_report_bridge_noise_all_viol_below_high.report
report_noise -nosplit -nworst 10 -below -high > $REPORTS_DIR/${DESIGN_NAME}_dmsa_report_bridge_noise_below_high.report


# ELMOS: added for transition patterns
remote_execute {
report_global_slack -significant_digits 4 -nosplit > $REPORTS_DIR/${DESIGN_NAME}_report_bridge_global_slack.report
}


##################################################################
#    Power Analysis Section                                      #
##################################################################
remote_execute {
## run power analysis
check_power   > $REPORTS_DIR/${DESIGN_NAME}_check_bridge_power.report
update_power 

## report_power
report_power > $REPORTS_DIR/${DESIGN_NAME}_report_bridge_power.report
}

##################################################################
#    SDF Generation                                              #
##################################################################
remote_execute {
write_sdf -context Verilog -version 3.0 -include {SETUPHOLD RECREM} -compress gzip \
          $RESULTS_DIR/$DESIGN_NAME.signoff.sdf.gz
}

##################################################################
#    Fix ECO Comments                                            #
##################################################################
# You can use -current_library option of fix_eco_drc and fix_eco_timing to use
# library cells only from the current library that the cell belongs to when sizing
#
# You can control the allowable area increase of the cell during sizing by setting the
# eco_alternative_area_ratio_threshold variable
#
# You can restrict sizing within a group of cells by setting the
# eco_alternative_cell_attribute_restrictions variable
#
# Refer to man page for more details



 


##################################################################
#    Fix ECO DRC Section                                         #
##################################################################
# Additional setup and hold margins can be preserved while fixing DRC with -setup_margin and -hold_margin
# Refer to man page for more details
# fix max transition 
#fix_eco_drc -type max_transition -method { size_cell insert_buffer } -verbose -buffer_list $eco_drc_buf_list 
# fix max capacitance 
#fix_eco_drc -type max_capacitance -method { size_cell insert_buffer } -verbose -buffer_list $eco_drc_buf_list 

##################################################################
#    Fix ECO Timing Section                                      #
##################################################################
# Path Based Analysis is supported for setup and hold fixing
#
# You can use -setup_margin and -hold_margin to add margins during 
# setup and hold fixing
#
# DRC can be ignored while fixing timing violations with -ignore_drc
#
# Refer to man page for more details
#
# Path specific and PBA based ECO can enabled via -path_selection_options
# See fix_eco_timing man page for more details path specific on PBA based timing fixing
# Reporting options should be changed to reflect path specific and PBA based ECO
#
# fix setup 
#fix_eco_timing -type setup -verbose -slack_lesser_than 0 -estimate_unfixable_reasons 
# fix hold 
#fix_eco_timing -type hold -verbose -buffer_list $eco_hold_buf_list -slack_lesser_than 0 -hold_margin 0 -setup_margin 0 -estimate_unfixable_reasons

#This is for power attribute flow for Scalar and DMSA
#fix_eco_timing -type hold -power_attribute <attr name>
#This is for leakage based flow for DMSA
#fix_eco_timing -type hold -power_mode leakage -leakage_scenario <scen_name>


##################################################################
#    Fix ECO Output Section                                      #
##################################################################
# write netlist changes
# ELMOS: write out only the merged version
#remote_execute {
#write_changes -format icctcl -output $RESULTS_DIR/eco_changes.tcl
#}










puts "RM-Info: Completed script [info script]\n"
