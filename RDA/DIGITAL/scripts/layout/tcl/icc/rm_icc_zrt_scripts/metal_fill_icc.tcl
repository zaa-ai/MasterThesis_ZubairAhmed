##########################################################################################
# Version: M-2016.12-SP4 (July 17, 2017)
# Copyright (C) 2010-2017 Synopsys, Inc. All rights reserved.
##########################################################################################

puts "RM-Info: Running script [info script]\n"

# ELMOS
# source -echo ./rm_setup/icc_setup.tcl 

###################################################
## chip_finish_icc: Several chipfinishing steps  ##
###################################################

open_mw_lib $MW_DESIGN_LIBRARY
redirect /dev/null "remove_mw_cel -version_kept 0 ${ICC_METAL_FILL_CEL}"
copy_mw_cel -from $ICC_CHIP_FINISH_CEL -to $ICC_METAL_FILL_CEL
open_mw_cel $ICC_METAL_FILL_CEL



source -echo common_optimization_settings_icc.tcl
source -echo common_placement_settings_icc.tcl
source -echo common_post_cts_timing_settings.tcl
source -echo common_route_si_settings_zrt_icc.tcl 

  if {$ICC_MCMM_METAL_FILL_SCENARIOS != ""} {
    set_active_scenarios $ICC_MCMM_METAL_FILL_SCENARIOS
  } else {
    set_active_scenarios [lminus [all_scenarios] [get_scenarios -setup false -hold false -cts_mode true]]
    ## Note: CTS only scenarios (get_scenarios -setup false -hold false -cts_mode true) are made inactive by RM during optimizations
  }

if { [check_error -verbose] != 0} { echo "RM-Error, flagging ..." }

if {$ADD_METAL_FILL != "NONE" } {
  ########################################
  #     REAL METAL FILL EXTRACTION       #
  ########################################
  ## Can be set to FLOATING|GROUNDED when required - default  = AUTO
  set_extraction_options -real_metalfill_extraction FLOATING

  if { [check_error -verbose] != 0} { echo "RM-Error, flagging ..." }
}
save_mw_cel -as $ICC_METAL_FILL_CEL

# ELMOS
if {[file exists [which $CUSTOM_METAL_FILL_PRE_SCRIPT]]} {
echo "RM-Info: Sourcing [which $CUSTOM_METAL_FILL_PRE_SCRIPT]"
source $CUSTOM_METAL_FILL_PRE_SCRIPT
}

## Note :
#  Use insert_metal_filler for technology nodes 65nm and above.
#  Use signoff_metal_fill for technology nodes 45nm and below.
if {$ADD_METAL_FILL == "ICC"} {
  ########################################
  #       TIMING DRIVEN METAL FILL       # 
  ########################################
  if {$ICC_METAL_FILL_TIMING_DRIVEN} {
    set_extraction_options -real_metalfill_extraction NONE
    insert_metal_filler -routing_space $ICC_METAL_FILL_SPACE -timing_driven
  } else {
    insert_metal_filler -routing_space $ICC_METAL_FILL_SPACE
  }

  set_extraction_options -real_metalfill_extraction FLOATING

  if { [check_error -verbose] != 0} { echo "RM-Error, flagging ..." }
}

if {$ADD_METAL_FILL == "ICV" } {
  ########################################
  #         ICV DRIVEN METAL FILL        # 
  ########################################
  if {[file exists [which $SIGNOFF_FILL_RUNSET]] } {
    set_physical_signoff_options -exec_cmd icv -fill_runset $SIGNOFF_FILL_RUNSET
  }
  if {$SIGNOFF_MAPFILE != ""} {set_physical_signoff_options -mapfile $SIGNOFF_MAPFILE}

  report_physical_signoff_options

  if { !$SIGNOFF_METAL_FILL_TIMING_DRIVEN } {
    signoff_metal_fill 
  } else {
    set_extraction_options -real_metalfill_extraction NONE

    ## To help meet the your required density in timing driven metal fill you can also 
    # apply the following option to signoff_metal_fill:
    #
    #  -fix_density_errors true
    #
    # You need to add minimum density rules to the tech file before adding this option. 
    # Check with your foundry for the density rules. 

    signoff_metal_fill -timing_preserve_setup_slack_threshold $TIMING_PRESERVE_SLACK_SETUP
  }

  set_extraction_options -real_metalfill_extraction FLOATING

  if { [check_error -verbose] != 0} { echo "RM-Error, flagging ..." }
}



if {$ICC_REPORTING_EFFORT == "MED" } {
 redirect -tee -file $REPORTS_DIR_METAL_FILL/$ICC_METAL_FILL_CEL.qor {report_qor}
 redirect -tee -file $REPORTS_DIR_METAL_FILL/$ICC_METAL_FILL_CEL.qor -append {report_qor -summary}
 redirect -file $REPORTS_DIR_METAL_FILL/$ICC_METAL_FILL_CEL.con {report_constraints}
}

if {$ICC_REPORTING_EFFORT != "OFF" } {
     if {[llength [get_scenarios -active true -setup true]]} {
     redirect -file $REPORTS_DIR_METAL_FILL/$ICC_METAL_FILL_CEL.clock_timing {report_clock_timing -nosplit -type skew -scenarios [get_scenarios -active true -setup true]} ;# local skew report
     redirect -tee -file $REPORTS_DIR_METAL_FILL/$ICC_METAL_FILL_CEL.max.clock_tree {report_clock_tree -nosplit -summary -scenarios [get_scenarios -active true -setup true]}     ;# global skew report
     }
     if {[llength [get_scenarios -active true -hold true]]} {
     redirect -tee -file $REPORTS_DIR_METAL_FILL/$ICC_METAL_FILL_CEL.min.clock_tree {report_clock_tree -nosplit -operating_condition min -summary -scenarios [get_scenarios -active true -hold true]}     ;# min global skew report
     }
}
if {$ICC_REPORTING_EFFORT != "OFF" } {
 redirect -file $REPORTS_DIR_METAL_FILL/$ICC_METAL_FILL_CEL.max.tim {report_timing -nosplit -crosstalk_delta -scenario [all_active_scenarios] -capacitance -transition_time -input_pins -nets -delay max} 
 redirect -file $REPORTS_DIR_METAL_FILL/$ICC_METAL_FILL_CEL.min.tim {report_timing -nosplit -crosstalk_delta -scenario [all_active_scenarios] -capacitance -transition_time -input_pins -nets -delay min} 
}
if {$ICC_REPORTING_EFFORT != "OFF" } {
 redirect -tee -file $REPORTS_DIR_METAL_FILL/$ICC_METAL_FILL_CEL.sum {report_design_physical -all -verbose}
}


if {$ICC_REPORTING_EFFORT != "OFF" } {
 create_qor_snapshot -clock_tree -name $ICC_METAL_FILL_CEL
 redirect -file $REPORTS_DIR_METAL_FILL/$ICC_METAL_FILL_CEL.qor_snapshot.rpt {report_qor_snapshot -no_display}
}

puts "RM-Info: Completed script [info script]\n"

# ELMOS: removed, leave it to the main script if we want to exit the tool here
#exit

