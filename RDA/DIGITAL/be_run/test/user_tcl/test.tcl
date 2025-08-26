puts "RM-Info: Running script [info script]\n"

source -echo user_tcl/test_setup.tcl

source -echo $env(PROJECT_HOME)/scripts/test/tcl/tmax/test_global_setup.tcl
source -echo $env(PROJECT_HOME)/scripts/test/tcl/tmax/test_build_setup.tcl
source -echo $env(PROJECT_HOME)/scripts/test/tcl/tmax/test_build.tcl
################################################################
##                     Dynamic Pattern                        ##
################################################################
source -echo $env(PROJECT_HOME)/scripts/test/tcl/tmax/test_td_drc.tcl
source -echo $env(PROJECT_HOME)/scripts/test/tcl/tmax/test_db_atpg.tcl
source -echo $env(PROJECT_HOME)/scripts/test/tcl/tmax/test_td_slack_atpg.tcl
source -echo $env(PROJECT_HOME)/scripts/test/tcl/tmax/test_td_atpg.tcl
source -echo $env(PROJECT_HOME)/scripts/test/tcl/tmax/test_ct_slack_atpg.tcl
source -echo $env(PROJECT_HOME)/scripts/test/tcl/tmax/test_ct_atpg.tcl
join_pattern_files dyn

################################################################
##                      Static Pattern                        ##
################################################################
source -echo $env(PROJECT_HOME)/scripts/test/tcl/tmax/test_sa_drc.tcl
source -echo $env(PROJECT_HOME)/scripts/test/tcl/tmax/test_sb_atpg.tcl
source -echo $env(PROJECT_HOME)/scripts/test/tcl/tmax/test_sa_atpg.tcl
source -echo $env(PROJECT_HOME)/scripts/test/tcl/tmax/test_cs_atpg.tcl
join_pattern_files stat

################################################################
##                       IDDQ Pattern                         ##
################################################################
# For serial iddq pattern we change tmax_file_ext to scan for better naming of files

set tmax_file_ext scan
if {$WITH_WRAPPER == ""} {
	set PROTOCOL_FILE  "../syn/results/digtop.mapped.iddq.spf" ;# IDDQ Mode STIL Protocol File
} else {
	set PROTOCOL_FILE  "./stil/digtop.mapped.iddq.spf_ATE_pins" ;# IDDQ Mode STIL Protocol File for ATE environment
}
source $env(PROJECT_HOME)/scripts/test/tcl/tmax/test_sa_drc.tcl
source $env(PROJECT_HOME)/scripts/test/tcl/tmax/test_id_atpg.tcl

puts "RM-Info: Completed script [info script]\n"

print_message_info

if {$env(QUIT) != 0} {
  exit
}
