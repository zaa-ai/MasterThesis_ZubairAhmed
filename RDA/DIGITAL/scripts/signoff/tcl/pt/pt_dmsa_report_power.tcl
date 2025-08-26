puts "RM-Info: Running script [info script]\n"
##################################################################
#    Power Analysis Section                                      #
##################################################################
# ELMOS: change to report power in every single corner
remote_execute {
## run power analysis
check_power   > $REPORTS_DIR/${DESIGN_NAME}_check_power.report
update_power 

## report_power
report_power > $REPORTS_DIR/${DESIGN_NAME}_report_power.report
}

puts "RM-Info: Completed script [info script]\n"
