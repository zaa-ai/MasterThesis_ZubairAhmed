puts "RM-Info: Running script [info script]\n"

source -echo $env(PROJECT_HOME)/scripts/misc/tcl/procs.tcl
source -echo user_tcl/common_setup.tcl

# Project specific overwrites of variables from common_setup
# remove non used libraries
set SCENARIO $env(SCENARIO)

if {[string match *_max $SCENARIO]} {
    set TARGET_LIBRARY_FILES      "[join [exec getPrjCfg.rb -r $TECH -p tech/lib/max\[@type='gates'\]]]"  ;#  Target technology logical libraries
    set ADDITIONAL_LINK_LIB_FILES "[join [exec getPrjCfg.rb -r $TECH -p tech/lib/max\[@type='macro'\]]]";# [exec getPrjCfg.rb -p tech/lib/no]"  ;#  Extra link logical libraries not included in TARGET_LIBRARY_FILES
    set PARASITIC_FILES           "results/digtop.starrc.spef.WCCOM.gz"
} elseif {[string match *_min $SCENARIO]} {
    set TARGET_LIBRARY_FILES      "[join [exec getPrjCfg.rb -r $TECH -p tech/lib/min\[@type='gates'\]]]"
    set ADDITIONAL_LINK_LIB_FILES "[join [exec getPrjCfg.rb -r $TECH -p tech/lib/min\[@type='macro'\]]]";# [exec getPrjCfg.rb -p tech/lib\[@type='macro'\]/no]"
    set PARASITIC_FILES           "results/digtop.starrc.spef.LTCOM.gz"
} else {
    puts "Error: scenario not found"
    exit
}
source ../syn/sdc/digtop.constraints.procs.tcl
set CONSTRAINT_FILES "../syn/sdc/digtop.constraints.${SCENARIO}.tcl"

source -echo $env(PROJECT_HOME)/scripts/signoff/tcl/pt/pt_setup.tcl
############################################################# 

# activate path based analysis, to get less pessimistic results
set ADDITIONAL_OPTIONS "-pba_mode exhaustive"

source -echo $env(PROJECT_HOME)/scripts/signoff/tcl/pt/pt_read_design.tcl
source -echo $env(PROJECT_HOME)/scripts/signoff/tcl/pt/pt_read_ba_constraints.tcl
source -echo $env(PROJECT_HOME)/scripts/signoff/tcl/pt/pt_setup_timing.tcl
source -echo $env(PROJECT_HOME)/scripts/signoff/tcl/pt/pt_check_timing.tcl
source -echo $env(PROJECT_HOME)/scripts/signoff/tcl/pt/pt_report_timing.tcl
source -echo $env(PROJECT_HOME)/scripts/signoff/tcl/pt/pt_report_power.tcl

#############################################################

# To have a short overview...
report_analysis_coverage

##################################################################
#    SDF Generation                                              #
##################################################################
write_sdf -context Verilog -version 3.0 -include {SETUPHOLD RECREM} -compress gzip \
          $RESULTS_DIR/$DESIGN_NAME.${SCENARIO}.signoff.sdf.gz

print_message_info

puts "RM-Info: Completed script [info script]\n"
if {$env(QUIT) != 0} {
  exit
}

