puts "RM-Info: Running script [info script]\n"

##########################
# Define CCD strategy
##########################

# To prevent Concurrent Clock and Data optimization from adjusting latency of boundary registers clock pins
# set_concurrent_clock_and_data_strategy -adjust_boundary_registers false

# Enable new clock gate modeling in "clock_opt -only_cts -concurrent_clock_and_data"
# set_app_var skew_opt_optimize_clock_gates true

# Enable TNS mode clock latency adjustments in "clock_opt -only_psyn -concurrent_clock_and_data"
# Note, "medium" tns_effort will result in higher clock buffer area compared to tns_effort "low"
# set_concurrent_clock_and_data_strategy -tns_effort medium

# Enable medium effort CCD FLOW for reducing CCD flow runtime.
set_concurrent_clock_and_data_strategy -effort $ICC_CLOCK_OPT_CCD_EFFORT 

report_concurrent_clock_and_data_strategy

# Enable update_clock_lateny throughout CCD flow
# set_app_var update_clock_latency_consider_float_pin_delays true

puts "RM-Info: Completed script [info script]\n"

