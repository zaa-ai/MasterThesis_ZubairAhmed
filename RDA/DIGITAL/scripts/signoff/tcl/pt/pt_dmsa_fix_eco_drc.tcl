puts "RM-Info: Running script [info script]\n"
##################################################################
#    Fix ECO Comments                                            #
##################################################################
# You can use -current_library option of fix_eco_drc and fix_eco_timing to use
# library cells only from the current library that the cell belongs to when sizing
#
# You can control the allowable area increase of the cell during sizing by setting the
# eco_alternative_area_ratio_threshold variable
#
# You can restrict sizing within a group of cells by setting the
# eco_alternative_cell_attribute_restrictions variable
#
# Refer to man page for more details



 


##################################################################
#    Fix ECO DRC Section                                         #
##################################################################
# Additional setup and hold margins can be preserved while fixing DRC with -setup_margin and -hold_margin
# Refer to man page for more details
# fix max transition 
fix_eco_drc -type max_transition -method { size_cell insert_buffer } -verbose -buffer_list $eco_drc_buf_list 
# fix max capacitance 
fix_eco_drc -type max_capacitance -method { size_cell insert_buffer } -verbose -buffer_list $eco_drc_buf_list 

puts "RM-Info: Completed script [info script]\n"
