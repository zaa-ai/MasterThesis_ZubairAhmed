
template : mesh_horizontal_above_tapcell(layer,net) { # PG template for power mesh generation
 layer : @layer {
	direction : vertical
	width : 0.56
	spacing : 52.46
	number : 15
	pitch : 
	offset_start : boundary	# user can also specify coordinate as {x y}
	offset_type : edge	# user can also specify edge 
	offset : 13.6
	trim_strap : true
 }
 advanced_rule : on { 
	stack_vias : all #all | adjacent | specified
	no_vias : off # do not create vias
	optimize_routing_tracks : on {
		layer : all       #layers to perform optimization
		alignment : true  #align straps to track or half-track
		sizing : true     #further size up straps w/o blocking more tracks
 	}
 	align_straps_with_physical_cell: on {
		layer :           @layer
		cell :            TAPCELLBWP7T
		pin :             @net
		direction :       vertical
		width :           0.56
		offset :          #offset from the center of pin
 	}
 	# Insert extra straps inside the channel area when on
	insert_channel_straps : off {
		# Layer name of the extra straps inserted. If not
		# specified, the tool uses the vertical layer from
		# the template
		#	layer : MET4
		# Width of the inserted straps, default is minimum
		#	width : 2
		# Spacing between inserted straps, default is minimum
		#	spacing : minimum
		# Minimum spacing for channel strap insertion, straps
		# are not inserted into channels narrower than
		# the specified value
		#	channel_threshold : 
		# Only check if there is strap of the specified layer
		# inside channel. If not, insert straps
		#	#check_one_layer : true 
		# Consider channels between placement blockages
		# and between placement blockage and macros. By default,
		# this directive is true and only
		# channels between macros are considered
		#	honor_placement_blockage : true
		# Consider channels between voltage areas
		# and between voltage areas and placement blockages.
		#	honor_voltage_area : false
		# Honor channels between hard keepout margins
		#	honor_keepout_margins : true
		# Space between boundary and macro or placement blockage is
		# considered a channel
		#	boundary_strap : true 
	}
 }
}


template : mesh_vertical(layer, spacing, pitch, offset_x, offset_y) { # PG template for power mesh generation
layer : @layer {
	direction : horizontal
	width : 0.56
	spacing : @spacing
	pitch : @pitch
	offset_start : {@offset_x @offset_y}	# user can also specify coordinate as {x y}
	offset_type : edge	# user can also specify centerline 
	offset : 0
	trim_strap : true
 }

advanced_rule : on {
	stack_vias : specified {
    connect_layers : {METAL4 METAL5}
    }
	no_vias : off # do not create vias
	optimize_routing_tracks : on {
		layer : @layer       #layers to perform optimization
		alignment : true  #align straps to track or half-track
		sizing : true     #further size up straps w/o blocking more tracks
 	}
 }
}

template : tapcell_horizontal { # PG template for substrate connection
#
# To add VSUB straps:
#
#layer : MTL4 {
#	direction : vertical
#	width : 2.880000
#	spacing : 2.00
#	number : 
#	pitch : 500
#	offset_start : boundary	# user can also specify coordinate as {x y}
#	offset_type : edge	# user can also specify centerline 
#	offset :
#	trim_strap : true
#}

  # Advanced rules for power plan creation
    advanced_rule : on { 
	stack_vias : all #all | adjacent | specified
	no_vias : off # do not create vias
	optimize_routing_tracks : off {
		layer : all       #layers to perform optimization
		alignment : true  #align straps to track or half-track
		sizing : true     #further size up straps w/o blocking more tracks
	}
	insert_channel_straps: off {
		layer :           #channel strap layer
		width : minimum   #channel strap width
		spacing : minimum #channel strap spacing
		channel_threshold: #ignore channels narrower than the threshold
		check_one_layer : false #only check straps in the specified layer
		boundary_strap : false #insert straps between region boundary
		honor_placement_blockage : true #honor channels between placement blocakges and macros
		honor_voltage_area : false #honor channels between voltage areas and macros
		honor_keepout_margins : true #honor channels between hard keepout margins
	}
	honor_max_stdcell_strap_distance : off {
		max_distance :    #maximum distance from stdcell to strap
		layer :           #additional strap layer
		offset :          #offset to the nearest straps
	}
	align_straps_with_power_switch : off {
		power_switch :    #specify power switch name to align
		layer :           #strap layer
		width :           #strap width
		direction :       #strap direction
		offset :          #offset from the center of pin
	}
	align_straps_with_stdcell_rail: off {
		layer :           #strap layer
		align_with_rail : false     #align strap with the rail
		put_strap_in_row : false    #put straps inside cell row
	}
	honor_advanced_via_rules : off
	align_straps_with_terminal_pin : off
	align_straps_with_physical_cell: on {
		layer :           MTL2
		cell :            gapfill2_lv
		direction :       vertical
		width :           0.56 
		offset :          #offset from the center of pin
	}
    }
}

#template : tapcell_vertical { # PG template for substrate connection
#
# To add VSUB straps:
#
#layer : MTL4 {
#	direction : horizontal
#	width : 2.880000
#	spacing : 2.00
#	number : 
#	pitch : 500
#	offset_start : boundary	# user can also specify coordinate as {x y}
#	offset_type : edge	# user can also specify centerline 
#	offset :
#	trim_strap : true
#}

  # Advanced rules for power plan creation
    advanced_rule : on { 
	stack_vias : all #all | adjacent | specified
	no_vias : off # do not create vias
	optimize_routing_tracks : off {
		layer : all       #layers to perform optimization
		alignment : true  #align straps to track or half-track
		sizing : true     #further size up straps w/o blocking more tracks
	}
	insert_channel_straps: off {
		layer :           #channel strap layer
		width : minimum   #channel strap width
		spacing : minimum #channel strap spacing
		channel_threshold: #ignore channels narrower than the threshold
		check_one_layer : false #only check straps in the specified layer
		boundary_strap : false #insert straps between region boundary
		honor_placement_blockage : true #honor channels between placement blocakges and macros
		honor_voltage_area : false #honor channels between voltage areas and macros
		honor_keepout_margins : true #honor channels between hard keepout margins
	}
	honor_max_stdcell_strap_distance : off {
		max_distance :    #maximum distance from stdcell to strap
		layer :           #additional strap layer
		offset :          #offset to the nearest straps
	}
	align_straps_with_power_switch : off {
		power_switch :    #specify power switch name to align
		layer :           #strap layer
		width :           #strap width
		direction :       #strap direction
		offset :          #offset from the center of pin
	}
	align_straps_with_stdcell_rail: off {
		layer :           #strap layer
		align_with_rail : false     #align strap with the rail
		put_strap_in_row : false    #put straps inside cell row
	}
	honor_advanced_via_rules : off
	align_straps_with_terminal_pin : off
	align_straps_with_physical_cell: on {
		layer :           MTL4
		cell :            WELLTAPS
		pin :             VSUB
		direction :       horizontal
		width :           1.44
		offset :          #offset from the center of pin
	}
    }
}