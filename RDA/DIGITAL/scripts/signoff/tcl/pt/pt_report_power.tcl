puts "RM-Info: Running script [info script]\n"
#################################################################################
# PrimeTime Reference Methodology Script
# Script: pt.tcl
# Version: P-2019.03-SP2 (July 1, 2019)
# Copyright (C) 2007-2019 Synopsys All rights reserved.
################################################################################

##################################################################  
#    Power Switching Activity: Vector Free Flow                  #  
##################################################################  
set power_default_toggle_rate 0.1 
set power_default_static_probability 0.5 
report_switching_activity           

##################################################################
#    Power Analysis Section                                      #
##################################################################
## run power analysis
check_power   > $REPORTS_DIR/${DESIGN_NAME}_${SCENARIO}_check_power.report
update_power  

## report_power
report_power > $REPORTS_DIR/${DESIGN_NAME}_${SCENARIO}_report_power.report

# Set 10% toggle rate on clock gates
set_switching_activity -clock_derate 0.1 -clock_domains [all_clocks] -type clock_gating_cells

# Clock Gating & Vth Group Reporting Section
report_clock_gate_savings  

# Set Vth attribute for each library if not set already
foreach_in_collection l [get_libs] {
        if {[get_attribute [get_lib $l] default_threshold_voltage_group] == ""} {
                set lname [get_object_name [get_lib $l]]
                set_user_attribute [get_lib $l] default_threshold_voltage_group $lname -class lib
        }
}
report_power -threshold_voltage_group > $REPORTS_DIR/${DESIGN_NAME}_${SCENARIO}_pwr.per_lib_leakage
report_threshold_voltage_group > $REPORTS_DIR/${DESIGN_NAME}_${SCENARIO}_pwr.per_volt_threshold_group

puts "RM-Info: Completed script [info script]\n"
