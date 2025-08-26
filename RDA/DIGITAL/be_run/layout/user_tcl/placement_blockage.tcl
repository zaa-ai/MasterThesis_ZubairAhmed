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


create_placement_blockage -coordinate [list [expr $BBOX_OTP_LLX - 305] [expr $BBOX_OTP_LLY - 175 ] [expr $BBOX_OTP_URX + 500 ] [expr $BBOX_OTP_URY + 140] ]  \
			  -name partial_block_right_of_OTP \
			  -type partial \
			  -blocked_percentage 50

#create_placement_blockage -coordinate [list [expr $BBOX_OTP_LLX - 200] [expr $BBOX_OTP_LLY - 20 ] [expr $BBOX_OTP_LLX ] [expr $BBOX_OTP_LLY + 70 ] ]  \
                          -name partial_block_beneath_the_IPS \
                          -type partial \
                          -blocked_percentage 30
# Workaraound to not place ROMNIBBLEs under PG-Straps (issues with metal shapes MET2/MET3 JIRA DS19-319; DS19-326)
#define_user_attribute -type boolean -class cell dont_place_under_pg_strap
#define_user_attribute -type boolean -class lib_cell dont_place_under_pg_strap
#set_attribute [get_flat_cells *ROMNIBBLE*] dont_place_under_pg_strap true
#create_placement_blockage -type partial -category dont_place_under_pg_strap \
   -blocked_percentage 50 -bbox {1510 0 1522 840} -name PB_for_ROMNIBBLE_cells
# Problem: When cells are placed overlapping these placement blockage the clock_opt step fails with an over utilization error.
# Idea: instead of restricting placement we can also try to place the module ic_revision in a dedicated voltage_are for placing.
# create_voltage_area 
   
   
   