###################################################################
# Macro Placement Script
# Could be created by write floorplan
# rename to "macro_place.tcl"
#- i_logic_top/i_data_storage/i_sram_3072x23u18 SRAM_3072X23U18 + PLACED ( 28050 17500 ) W
#- i_logic_top/i_test_top/i_otp_wrapper/u_otpwrap_l3_top/u_otpwrap_l2_cpu/u_otpwrap_l1_jtag/u_otpwrap_l0_atpg/u_otp4kx12/u_ips ips_tsmc180bcd50_p1r_ad + PLACED ( 939005 920500 ) FN
#- i_logic_top/i_test_top/i_otp_wrapper/u_otpwrap_l3_top/u_otpwrap_l2_cpu/u_otpwrap_l1_jtag/u_otpwrap_l0_atpg/u_otp4kx12/u_otp4kx12 slp_b_tsmc180bcd50_4kx12_cm16d_ab_r20 + PLACED ( 1384045 858285 ) FE
#- i_digital_iso digital_iso + PLACED ( 0 0 ) N
##################################################################
undo_config -disable
set oldSnapState [set_object_snap_type -enabled false]
set_object_snap_type -snap litho -class hard_macro
remove_dont_touch_placement [all_macro_cells ]

# RAM
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
cut_row -within [list [expr $BBOX_RAM_LLX - 18.5] [expr $BBOX_RAM_LLY - 17.5] [expr $BBOX_RAM_URX + 18.5] [expr $BBOX_RAM_URY + 18.5]]

# IPS integrated Power Supply for OTP

set obj $IPS_INST
#set_attribute -quiet $obj orientation N
#set_attribute -quiet $obj origin {0.020 1929.87}
set_attribute -quiet $obj is_placed true
set_attribute -quiet $obj is_fixed true
set_attribute -quiet $obj is_soft_fixed false
set_attribute -quiet $obj eco_status eco_reset

set BBOX_IPS_LLX [get_attribute $obj bbox_llx]
set BBOX_IPS_LLY [get_attribute $obj bbox_lly]
set BBOX_IPS_URX [get_attribute $obj bbox_urx]
set BBOX_IPS_URY [get_attribute $obj bbox_ury]
cut_row -within [list [expr $BBOX_IPS_LLX - 25] [expr $BBOX_IPS_LLY - 16] [expr $BBOX_IPS_URX + 23.25 ] [expr $BBOX_IPS_URY + 16]]

# OTP 4kx12 one time programmable memory

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
cut_row -within [list [expr $BBOX_OTP_LLX - 25] [expr $BBOX_OTP_LLY - 24.7] [expr $BBOX_OTP_URX + 20] [expr $BBOX_OTP_URY + 24.7]]

set obj i_digital_iso
set_attribute -quiet $obj orientation N
set_attribute -quiet $obj origin {0 0}
set_attribute -quiet $obj is_placed true
set_attribute -quiet $obj is_fixed true

set_dont_touch_placement [all_macro_cells ]

set_object_snap_type -enabled $oldSnapState

undo_config -enable
	
