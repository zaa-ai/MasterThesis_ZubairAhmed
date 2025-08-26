set_fix_hold [all_clocks]

route_opt -incremental -only_hold_time -effort high


#relaxing the existing placement blockages a little bit
# User defined placement blockages
# This script is sourced in custom_dp_script.tcl
# Placementblockage in the upper right corner for bettern routing results
set obj $OTP_INST
#set_attribute -quiet $obj orientation N
#set_attribute -quiet $obj origin {0.020 1987.91}
set_attribute -quiet $obj is_placed true
set_attribute -quiet $obj is_fixed true
set_attribute -quiet $obj is_soft_fixed false
set_attribute -quiet $obj eco_status eco_reset

set BBOX_OTP_LLX [get_attribute $obj bbox_llx]
set BBOX_OTP_LLY [get_attribute $obj bbox_lly]
set BBOX_OTP_URX [get_attribute $obj bbox_urx]
set BBOX_OTP_URY [get_attribute $obj bbox_ury]

remove_placement_blockage -name partial_block_right_of_OTP; # was partial with 40 percent blockage
remove_placement_blockage -name partial_block_beneath_the_IPS; # was partial with 20 percent blockage

#create_placement_blockage -coordinate [list [expr $BBOX_OTP_URX] [expr $BBOX_OTP_LLY - 20 ] [expr $BBOX_OTP_URX + 120 ] [expr $BBOX_OTP_URY] ]  \
-name partial_block_right_of_OTP \
-type partial \
-blocked_percentage 30

#create_placement_blockage -coordinate [list [expr $BBOX_OTP_LLX - 200] [expr $BBOX_OTP_LLY - 20 ] [expr $BBOX_OTP_LLX ] [expr $BBOX_OTP_LLY + 70 ] ]  \
-name partial_block_beneath_the_IPS \
-type partial \
-blocked_percentage 10

proc DRCerrorCount {} {
  set drcAll     [sizeof_collection [get_drc_errors -quiet]]
  set drcAntenna [sizeof_collection [get_drc_errors -quiet -filter "type == Antenna"]]
  return [expr $drcAll - $drcAntenna]
}

set DRcount 1
while {([DRCerrorCount] > 1) && ([DRCerrorCount] < 1000) && ($DRcount < 20)} {
  puts "Custom Loop: remaining DRC violations: [DRCerrorCount]; start $DRcount round of incremental routing"
  route_zrt_detail -incremental true
  incr DRcount
}

