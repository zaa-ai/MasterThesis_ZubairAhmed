set obj $SRAM_INST
#set_attribute -quiet $obj orientation E
#set_attribute -quiet $obj origin {710.565 17.5}
set_attribute -quiet $obj is_placed true
set_attribute -quiet $obj is_fixed true
set_attribute -quiet $obj is_soft_fixed false
set_attribute -quiet $obj eco_status eco_reset

set BBOX_RAM_LLX [get_attribute $obj bbox_llx]
set BBOX_RAM_LLY [get_attribute $obj bbox_lly]
set BBOX_RAM_URX [get_attribute $obj bbox_urx]
set BBOX_RAM_URY [get_attribute $obj bbox_ury]

create_route_guide -name route_guide_0 -no_signal_layers {METAL1} -coordinate [list [expr $BBOX_RAM_URX -1 ] [expr $BBOX_RAM_LLY] [expr $BBOX_RAM_URX + 5] [expr $BBOX_RAM_URY]]

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



remove_placement_blockage -name partial_block_right_of_OTP; # was partial with 50 percent blockage
remove_placement_blockage -name partial_block_beneath_the_IPS; # was partial with 30 percent blockage

create_placement_blockage -coordinate [list [expr $BBOX_OTP_URX] [expr $BBOX_OTP_LLY - 20 ] [expr $BBOX_OTP_URX + 120 ] [expr $BBOX_OTP_URY] ]  \
-name partial_block_right_of_OTP \
-type partial \
-blocked_percentage 40

create_placement_blockage -coordinate [list [expr $BBOX_OTP_LLX - 200] [expr $BBOX_OTP_LLY - 20 ] [expr $BBOX_OTP_LLX ] [expr $BBOX_OTP_LLY + 70 ] ]  \
-name partial_block_beneath_the_IPS \
-type partial \
-blocked_percentage 20
