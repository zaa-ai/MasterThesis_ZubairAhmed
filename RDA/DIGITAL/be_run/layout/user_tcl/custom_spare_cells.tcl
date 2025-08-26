# #####################################################
# Flow Version 3
# #####################################################
#
# $Date: 2016-11-07 17:44:25 +0100 (Mon, 07 Nov 2016) $
# $Rev: 2394 $:
# $Author: rk $
# #####################################################
#
#
# Define Space Cell Configuration here
#
#
#insert_spare_cells -lib_cell {NAND3 NOR3 DFCRLQ} -cell_name spares -num_instances 5 -tie
#insert_spare_cells -lib_cell {NAND3X2 NOR3X2 SEDFFX2} -cell_name spares -num_instances 5 -tie
insert_spare_cells 	-lib_cell {INVD2BWP7T ND4D2BWP7T NR4D2BWP7T NR2D1BWP7T ND2D2BWP7T SDFCND1BWP7T} \
			-cell_name spares \
			-num_instances 20 \
			-tie \
			-skip_legal
			
legalize_placement
