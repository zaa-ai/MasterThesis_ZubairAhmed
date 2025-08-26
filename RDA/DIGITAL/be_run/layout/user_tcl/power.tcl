# recreate every preexisting route guide, which only have attribute no_signal_layers defined
#return -level 4
foreach_in_collection rg [get_route_guides *] {
  set pre_lay [get_attribute -quiet $rg no_preroute_layers]

  if {$pre_lay == ""} {
    set name    [get_object_name $rg]
    set sig_lay [get_attribute $rg no_signal_layers]
    set bbox    [get_attribute $rg bbox]

    create_route_guide -name "pre_${name}"            \
                       -coordinate $bbox              \
                       -no_preroute_layers $sig_lay
  }
}

set PWR_NETS "$MW_POWER_NET $MW_GROUND_NET"

#to have stdcells for preroute
    insert_stdcell_filler -cell_without_metal $FILLER_CELL               \
        -connect_to_power $MW_POWER_NET -connect_to_ground $MW_GROUND_NET

# to have place for connection between via wall of power rails and signal pins of SRAM 
 #set obj $SRAM_INST
 #set llx [expr [get_attribute $obj bbox_llx]]
 #set lly [expr [get_attribute $obj bbox_lly]]
 #set urx [expr [get_attribute $obj bbox_urx]]
 #set ury [expr [get_attribute $obj bbox_ury]]
 #set bbox_sram [list [expr $urx ] [expr $lly] [expr $urx - 38] [expr $ury]]
 
 #create_routing_blockage -layers {metal2Blockage metal3Blockage metal4Blockage} -bbox $bbox_sram
 #create_route_guide 	-coordinate $bbox_sram \
 			-name POWER_RBL_SRAM \
 			-no_signal_layers {METAL1 METAL2 METAL3 METAL4 METAL5 } \
 			-no_preroute_layers {METAL1 METAL2 METAL3 METAL4 METAL5} \
 			-zero_min_spacing

# to not route connection for power rails over OTP
 set obj $OTP_INST
 set llx [expr [get_attribute $obj bbox_llx]]
 set lly [expr [get_attribute $obj bbox_lly]]
 set urx [expr [get_attribute $obj bbox_urx]]
 set ury [expr [get_attribute $obj bbox_ury]]
 set bbox_otp [list [expr $llx - 17.5] [expr $lly - 17.5] [expr $urx + 5] [expr $ury +17.5]]

 create_route_guide 	-name POWER_RBL_OTP   \
			-coordinate $bbox_otp \
			-no_preroute_layers {METAL1 METAL2 METAL3 METAL4 METAL5}

# Creating advanced via rule to limit the with of PG Via Walls for better QoR
set_preroute_advanced_via_rule -move_via_to_center -size_by_array_dimensions {5 1}
preroute_standard_cells -nets $PWR_NETS -remove_floating_pieces -advanced_via_rules

#remove_route_guide POWER_RBL_SRAM
remove_route_guide POWER_RBL_OTP

remove_stdcell_filler -stdcell
 
#Power Mesh
#create_pns_pg created in gui with PNS
source user_tcl/create_pns_pg.tcl
