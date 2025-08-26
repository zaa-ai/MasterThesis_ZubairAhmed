puts "RM-Info: Running script [info script]\n"
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
fix_eco_timing -type setup -verbose -slack_lesser_than 0 -estimate_unfixable_reasons 
# fix hold 
fix_eco_timing -type hold -verbose -buffer_list $eco_hold_buf_list -slack_lesser_than 0 -hold_margin 0 -setup_margin 0 -estimate_unfixable_reasons

#This is for power attribute flow for Scalar and DMSA
#fix_eco_timing -type hold -power_attribute <attr name>
#This is for leakage based flow for DMSA
#fix_eco_timing -type hold -power_mode leakage -leakage_scenario <scen_name>


puts "RM-Info: Completed script [info script]\n"
