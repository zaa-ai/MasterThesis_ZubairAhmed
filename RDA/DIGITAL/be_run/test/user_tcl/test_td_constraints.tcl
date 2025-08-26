puts "-------------------------------------------------------------------------------"
puts "RM-Info: Running script [info script]"
puts "-------------------------------------------------------------------------------"

# Set constraints on the Primary Inputs (top-level inputs) here.
# Normally scan enables and resets must be inactive when testing transition delay faults.
# All scan enables and resets must be inactive for Power-Aware ATPG,
# except that resets may pulse if set_atpg -power_effort high is used.
#
# Uncomment with proper port names and off states.
# add_pi_constraints 0 <input_port>
# add_pi_constraints 0 test_se
# add_pi_constraints 1 reset_n

# ELMOS: SCAN_ENABLE and SCAN_RES shall be stable during transition clock phase!
if {$SCAN_ENABLE != ""} {add_pi_constraints 0 $SCAN_ENABLE}
if {$SCAN_RES != ""}    {add_pi_constraints 1 $SCAN_RES}

puts "-------------------------------------------------------------------------------"
puts "RM-Info: Completed script [info script]"
puts "-------------------------------------------------------------------------------"
