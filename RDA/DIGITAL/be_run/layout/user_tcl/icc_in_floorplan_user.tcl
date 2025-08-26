read_def -verbose -no_incremental -snet_no_shape_as_user_enter $ICC_IN_DEF_FILE

#slightly more than the digital_iso cell because of keepout margin (in icc cell-> keepout)
set left_io2core 13.7 
set right_io2core 13.7
set top_io2core 13.5
set bottom_io2core 13.7

initialize_rectilinear_block \
	-use_current_boundary \
	-flip_first_row \
	-keep_io_place \
	-keep_macro_place \
	-left_io2core $left_io2core -right_io2core $right_io2core -top_io2core $top_io2core -bottom_io2core $bottom_io2core

#return -level 3

source -echo user_tcl/macro_place.tcl
source -echo user_tcl/connect_pg_nets.tcl

###############################################################################
# Hard placement blockages caused by pwell digital_iso
###############################################################################
			  
#create_placement_blockage -coordinate {{0.008 0.000} {12.230 1929.600}} -name block_left_side_hard -type hard
#create_placement_blockage -coordinate {{4.230 0.000} {215.430 14.400}} -name bottom_left_side_hard -type hard
#create_placement_blockage -coordinate {{240.230 1936.800} {793.745 1951.200}} -name upper_side_hard -type hard

#create_placement_blockage -coordinate {{675.430 856.400} {725.030 1094.400}} \
#-name fill_cap_under_power_rails \
#-type hard
source -echo user_tcl/global_settings.tcl
source -echo user_tcl/power.tcl
source -echo user_tcl/custom_dp_script.tcl
source -echo user_tcl/placement_blockage.tcl

###############################################################################
# Routing blockage MTL1-MTL4 caused by SRAM protection layer
###############################################################################
#
#create_routing_blockage -layers {metal1Blockage via1Blockage metal2Blockage via2Blockage metal3Blockage via3Blockage metal4Blockage} -bbox {{831.630 5.800} {1868.830 6.600}}	
#create_routing_blockage -layers {metal1Blockage via1Blockage metal2Blockage via2Blockage metal3Blockage via3Blockage metal4Blockage} -bbox {{830.830 6.000} {831.630 356.200}}
#create_routing_blockage -layers {metal1Blockage via1Blockage metal2Blockage via2Blockage metal3Blockage via3Blockage metal4Blockage} -bbox {{1868.830 5.800} {1869.630 356.200}}
#
#remove_placement_blockage -name fill_cap_under_power_rails
#remove_placement_blockage -name blockage_left_main_power_rails_for_filler
#remove_placement_blockage -name blockage_between_rom_and_ram
