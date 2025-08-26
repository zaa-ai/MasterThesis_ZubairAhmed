# #####################################################
# Flow Version 3
# #####################################################
# icc_dp_tpns.tcl
# $Date: 2016-11-07 17:44:25 +0100 (Mon, 07 Nov 2016) $
# $Rev: 2394 $:
# $Author: rk $
# #####################################################
###################################################
#   Power Network Synthesis
#   =======================
#   Add here Power Ring and Mesh creation Commands
#
###################################################

set PWR_NETS [list $MW_POWER_NET $MW_GROUND_NET ]

if {$EL_VERT_ROW} {
  set ROW_ORIENT vertical
} else {
  set ROW_ORIENT horizontal
}

####################################
# Core Ring 
####################################

derive_pg_connection -power_net $MW_POWER_NET -power_pin $MW_POWER_PORT -ground_net $MW_GROUND_NET -ground_pin $MW_GROUND_PORT -create_port top 

if {$EL_BOUNDARY == FALSE} {
  synthesize_fp_rings -nets $PWR_NETS -core -width {6 6}
  #create_rectangular_rings  -width {5 5} -nets  {VDD VSS}
  #-width {5 5} -layers {MTL1 MTL2} \
  #-offset {1 1}
} else {

  set p1 [get_attribute [get_core_area] points]
  create_power_plan_regions pp_region1 -polygon $p1

  set_power_ring_strategy str_m2m3 -nets $MW_POWER_NET -power_plan_regions {pp_region1} \
      -template rm_icc_dp_scripts/ring.tpl:ring_m2m3_${ROW_ORIENT}(14.0,4.0,minimum)
  compile_power_plan -ring -strategy str_m2m3

  set_power_ring_strategy str_m3m4 -nets $MW_GROUND_NET -power_plan_regions {pp_region1} \
      -template rm_icc_dp_scripts/ring.tpl:ring_m3m4_${ROW_ORIENT}(20.0,4.0,minimum)
  compile_power_plan -ring -strategy str_m3m4
}

####################################
# Opt. VSUB Ring
####################################

if {$EL_VSUB} {
  echo "--> Substrate connected to VSUB "

  set p2 [get_attribute [get_die_area] boundary]
  create_power_plan_regions pp_region2 -polygon $p2

  set_power_ring_strategy vs -nets $MW_SUB_NET -power_plan_regions {pp_region2} \
      -template rm_icc_dp_scripts/ring.tpl:vsub_ring_${ROW_ORIENT}
  compile_power_plan -ring -strategy vs
}

####################################
# Macros: EXAMPLE
# Macro Rings
####################################
#set RING_NETS [concat $PWR_NETS $MW_SUB_NET]
#set_power_ring_strategy pg_rom0 -macros {rom_wrapper_inst/u_rom2k16_c0/rom2kx16u35c0_s_inst} \
#    -nets $RING_NETS -template rm_icc_dp_scripts/ring.tpl:block_ring -skip {sides: {1 2 3}} -extension  {{direction:L} }
#set_power_ring_strategy pg_rom1 -macros {rom_wrapper_inst/u_rom2k16_c1/rom2kx16u35c1_s_inst} \
#    -nets $RING_NETS -template rm_icc_dp_scripts/ring.tpl:block_ring -skip {sides: {1 2 3}} -extension  {{direction:L} }
#set_power_ring_strategy pg_rom2 -macros {rom_wrapper_inst/u_rom2k16_c2/rom2kx16u35c2_s_inst} \
#    -nets $RING_NETS -template rm_icc_dp_scripts/ring.tpl:block_ring -skip {sides: {1 2 }} -extension  {{direction:LT} }
#set_power_ring_strategy pg_rom3 -macros {rom_wrapper_inst/u_rom2k16_s/rom2kx16u35s_s_inst } \
#    -nets $RING_NETS -template rm_icc_dp_scripts/ring.tpl:block_ring -skip {sides: {1 4}} -extension  {{direction:BL} }

#compile_power_plan -ring -strategy pg_rom0
#compile_power_plan -ring -strategy pg_rom1
#compile_power_plan -ring -strategy pg_rom2
#compile_power_plan -ring -strategy pg_rom3


#set_power_ring_strategy pg_ram -macros {ram_wrapper_inst/RAM512X8U35_S_INST} \
#    -nets $RING_NETS -template rm_icc_dp_scripts/ring.tpl:block_ring -skip {sides: {2 3}} -extension  {{direction:TR} }

#set_power_ring_strategy pg_ee0 -macros {eeprom_wrapper_inst/ee128x12stgu35j_ctr_inst/u_ee64x12_0 } \
#    -nets $RING_NETS -template rm_icc_dp_scripts/ring.tpl:block_ring -skip {sides: {4 3}} -extension  {{direction:B} }
#set_power_ring_strategy pg_ee1 -macros {eeprom_wrapper_inst/ee128x12stgu35j_ctr_inst/u_ee64x12_1} \
#    -nets $RING_NETS -template rm_icc_dp_scripts/ring.tpl:block_ring -skip {sides: {1 4 3}} -extension  {{direction:LR} }

#compile_power_plan -ring -strategy pg_ram
#compile_power_plan -ring -strategy pg_ee0
#compile_power_plan -ring -strategy pg_ee1

####################################
# Opt. VSUB Mesh
####################################

if {$EL_VSUB} {
  set_power_plan_strategy tapcell_strategy \
	-nets $MW_SUB_NET -core -template rm_icc_dp_scripts/mesh.tpl:tapcell_${ROW_ORIENT} \
	-extension {{{nets:$MW_SUB_NET} {direction:LRTB} {stop:first_target}}}
  compile_power_plan -strategy tapcell_strategy
} else {
  echo "--> Substrate connected to GND "
}

####################################
# Std. Cells  / Macros
####################################
#

preroute_standard_cells -nets $PWR_NETS -fill_empty_rows \
        -connect $ROW_ORIENT -port_filter_mode off \
        -cell_master_filter_mode off -cell_instance_filter_mode off \
        -voltage_area_filter_mode off -route_type {P/G Std. Cell Pin Conn} -do_not_route_over_macros

####################################
# Generate Mesh
####################################
#
set_power_plan_strategy pg_mesh1 -core -nets $POW_NETS -template rm_icc_dp_scripts/mesh.tpl:mesh_${ROW_ORIENT}(METAL4) -extension {{stop: innermost_ring}}
compile_power_plan -strategy pg_mesh1
preroute_instances  -ignore_pads -ignore_cover_cells