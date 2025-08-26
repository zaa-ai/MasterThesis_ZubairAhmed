puts "RM-Info: Running script [info script]\n"

source -echo user_tcl/test_setup.tcl

# Overwrite $NETLIST_FILES from test_setup.tcl
# Because we running on synthesis net list file ....
set NETLIST_FILES           "../syn/results/digtop.mapped.v " ;# Design files, faulted inside modules (default: DC-RM output)

source -echo $env(PROJECT_HOME)/scripts/test/tcl/tmax/test_global_setup.tcl
source -echo $env(PROJECT_HOME)/scripts/test/tcl/tmax/test_build_setup.tcl
source -echo $env(PROJECT_HOME)/scripts/test/tcl/tmax/test_build.tcl

################################################################
##                      Static Pattern                        ##
################################################################
source -echo $env(PROJECT_HOME)/scripts/test/tcl/tmax/test_sa_drc.tcl
set TMAX_OPTIMIZE_PATTERNS TRUE
source -echo $env(PROJECT_HOME)/scripts/test/tcl/tmax/test_sa_atpg.tcl
join_pattern_files stat

puts "RM-Info: Completed script [info script]\n"

print_message_info

if {$env(QUIT) != 0} {
  exit
}

gui_start
