puts "RM-Info: Running script [info script]\n"
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
# ELMOS: added ADDITIONAL_OPTIONS to report_(global)_timing and report_constraints
eval report_global_timing ${ADDITIONAL_OPTIONS} > $REPORTS_DIR/${DESIGN_NAME}_dmsa_report_global_timing.report
eval report_timing ${ADDITIONAL_OPTIONS} -crosstalk_delta -slack_lesser_than 0.0 -delay min_max -nosplit -input -net -sign 4 > $REPORTS_DIR/${DESIGN_NAME}_dmsa_report_timing.report

# ELMOS: added details for untested paths
report_analysis_coverage -status_details {untested} -nosplit > $REPORTS_DIR/${DESIGN_NAME}_dmsa_report_analysis_coverage.report 

remote_execute {
report_clock -skew -attribute > $REPORTS_DIR/${DESIGN_NAME}_report_clock.report 
# Clock Network Double Switching Report
report_si_double_switching -nosplit -rise -fall > $REPORTS_DIR/${DESIGN_NAME}_report_si_double_switching.report
}
eval report_constraints ${ADDITIONAL_OPTIONS} -all_violators -verbose > $REPORTS_DIR/${DESIGN_NAME}_dmsa_report_constraints.report
remote_execute {
eval report_constraints ${ADDITIONAL_OPTIONS} -all_violators -verbose > $REPORTS_DIR/${DESIGN_NAME}_report_constraints.report
report_design > $REPORTS_DIR/${DESIGN_NAME}_report_design.report
report_net > $REPORTS_DIR/${DESIGN_NAME}_report_net.report
}

# Noise Settings
remote_execute {
set_noise_parameters -enable_propagation -analysis_mode report_at_endpoint
check_noise > $REPORTS_DIR/${DESIGN_NAME}_check_noise.report
update_noise

# Noise Reporting
report_noise -nosplit -all_violators -above -low > $REPORTS_DIR/${DESIGN_NAME}_report_noise_all_viol_abv_low.report
report_noise -nosplit -nworst 10 -above -low > $REPORTS_DIR/${DESIGN_NAME}_report_noise_alow.report

report_noise -nosplit -all_violators -below -high > $REPORTS_DIR/${DESIGN_NAME}_report_noise_all_viol_below_high.report
report_noise -nosplit -nworst 10 -below -high > $REPORTS_DIR/${DESIGN_NAME}_report_noise_below_high.report

}

# Merged Noise Reporting
report_noise -nosplit -all_violators -above -low > $REPORTS_DIR/${DESIGN_NAME}_dmsa_report_noise_all_viol_abv_low.report
report_noise -nosplit -nworst 10 -above -low > $REPORTS_DIR/${DESIGN_NAME}_dmsa_report_noise_alow.report

report_noise -nosplit -all_violators -below -high > $REPORTS_DIR/${DESIGN_NAME}_dmsa_report_noise_all_viol_below_high.report
report_noise -nosplit -nworst 10 -below -high > $REPORTS_DIR/${DESIGN_NAME}_dmsa_report_noise_below_high.report


# ELMOS: added for transition patterns
remote_execute {
report_global_slack -significant_digits 4 -nosplit > $REPORTS_DIR/${DESIGN_NAME}_report_global_slack.report
}


puts "RM-Info: Completed script [info script]\n"
