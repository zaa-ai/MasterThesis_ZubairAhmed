puts "RM-Info: Running script [info script]\n"
##################################################################
#    Fix ECO Output Section                                      #
##################################################################
# write netlist changes
# ELMOS: write out only the merged version
#remote_execute {
write_changes -format icctcl -output $RESULTS_DIR/eco_changes.tcl
#}










puts "RM-Info: Completed script [info script]\n"
