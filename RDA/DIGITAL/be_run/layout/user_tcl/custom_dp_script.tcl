# custom_icc_dp_place_constraint_script.tcl
# ====================
# Add and place tap filler cells
# Manually add and place decaps in specific regions
# Add placement blockages for better routing resultst

derive_pg_connection -power_net $MW_POWER_NET -power_pin $MW_POWER_PORT -ground_net $MW_GROUND_NET -ground_pin $MW_GROUND_PORT -create_port top
###############################################################################
# Place Tapcells
###############################################################################
# Tap distance is dependend from technology and the pattern used for add_tap_cell_array
set TAP_DISTANCE  52.8

echo "Adding TAP cells with normal connection to Ground"
add_tap_cell_array -master_cell_name $TAPCELLNAME \
    -distance $TAP_DISTANCE \
    -pattern stagger_every_other_row \
    -substrate_port_name $MW_GROUND_NET \
    -substrate_net_name $MW_GROUND_NET \
    -connect_power_name $MW_POWER_NET \
    -connect_ground_name $MW_GROUND_NET \
    -fill_boundary_row false \
    -fill_macro_blockage_row false \
    -macro_blockage_row_double_density false \
    -respect_keepout

#    -left_macro_blockage_extra_tap must_insert \
#    -right_macro_blockage_extra_tap must_insert \
#    -left_boundary_extra_tap must_insert \
#    -right_boundary_extra_tap must_insert \

###############################################################################
# Add decapcells in specific regions
###############################################################################
set BLOCK_PLACEMENT_AROUND_MACROS true
if {${BLOCK_PLACEMENT_AROUND_MACROS}} {

    set obj $SRAM_INST
    set llx [expr [get_attribute $obj bbox_llx]]
    set lly [expr [get_attribute $obj bbox_lly] -10]
    set urx [expr [get_attribute $obj bbox_urx] + 27]
    set ury [expr [get_attribute $obj bbox_ury] + 10]
    set bbox [list [list $llx $lly] [list $urx $ury]]
    insert_stdcell_filler -cell_without_metal $FILLER_CELL_METAL -respect_keepout -connect_to_power $MW_POWER_NET -connect_to_ground $MW_GROUND_NET -bounding_box $bbox
    set_attribute -class cell [get_cells -within $bbox -all] is_fixed true
}

set BLOCK_PLACEMENT_UNDER_POWER_STRAPS 1
if {${BLOCK_PLACEMENT_UNDER_POWER_STRAPS}} {
    set rowH 3.92;#ToDo: Check with your current technology
    set cellW 1.68;#ToDo: Check with your current technology
    #set rowOffset -12
    foreach_in_collection WIRE [get_net_shape -filter {(owner_net=="VDD" || owner_net=="VSS")  && (layer=="METAL4" || layer=="METAL2" || layer=="METAL5") && (width>="10")}] {
    	set llx [expr [get_attribute $WIRE bbox_llx] - $cellW]
        set lly [expr [get_attribute $WIRE bbox_lly] - $rowH]
        set urx [expr [get_attribute $WIRE bbox_urx] + $cellW]
        set ury [expr [get_attribute $WIRE bbox_ury] + $rowH]
        set bbox [list [list $llx $lly] [list $urx $ury]]
        insert_stdcell_filler -cell_without_metal $FILLER_CELL_METAL -respect_keepout -connect_to_power $MW_POWER_NET -connect_to_ground $MW_GROUND_NET -bounding_box $bbox
        set_attribute -class cell [get_cells -within $bbox -all] is_fixed true
    }
    foreach_in_collection WIRE [get_net_shape -filter {(owner_net=="VCC") && (layer=="METAL4") && (width>="10")}] {
	set llx [expr [get_attribute $WIRE bbox_llx] + $cellW]
	set lly [expr [get_attribute $WIRE bbox_lly] - $rowH]
	set urx [expr [get_attribute $WIRE bbox_urx] - $cellW]
	set ury [expr [get_attribute $WIRE bbox_ury] + $rowH]
	set bbox [list [list $llx $lly] [list $urx $ury]]
	insert_stdcell_filler -cell_without_metal $FILLER_CELL_METAL -respect_keepout -connect_to_power $MW_POWER_NET -connect_to_ground $MW_GROUND_NET -bounding_box $bbox
	set_attribute -class cell [get_cells -within $bbox -all] is_fixed true
    }
}
