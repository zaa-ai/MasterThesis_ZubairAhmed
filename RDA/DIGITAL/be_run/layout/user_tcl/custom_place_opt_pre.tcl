## magnet placement of macro cells output to avoid max trans violations
magnet_placement [get_flat_pins -of_objects [get_flat_cells $OTP_INST]  -filter "direction == out"]
magnet_placement [get_flat_pins -of_objects [get_flat_cells $IPS_INST]  -filter "direction == out"]
magnet_placement [get_flat_pins -of_objects [get_flat_cells $SRAM_INST] -filter "direction == out"]

create_placement -congestion -congestion_effort high

# To not have shorts of P/G-Vias and Pins of ROM_NIBBLE cells
# JIRA DS19-326
# user attribute definition
define_user_attribute -type boolean -class lib_cell my_attr
define_user_attribute -type boolean -class cell my_attr
#
# # apply user attribute to ROM_Nibble cell
set_attribute ROMNIBBLE* my_attr true
set_attribute tcb018gbwp7t_rom_bc/ROMNIBBLE* my_attr true
set_attribute tcb018gbwp7t_rom_wc/ROMNIBBLE* my_attr true
#
# # get PG straps shapes
set shapes [get_net_shapes -filter {route_type == "pg_strap"}]
#
# # create placement blockages for each PG strap
set i 0
 foreach_in_collection shape $shapes {
   set bbx [get_attr $shape bbox]
     puts $bbx
       create_placement_blockage -type partial -category my_attr1 -blocked_percentage 70 -bbox $bbx -name my_category_blockage_$i
         incr i
 }

