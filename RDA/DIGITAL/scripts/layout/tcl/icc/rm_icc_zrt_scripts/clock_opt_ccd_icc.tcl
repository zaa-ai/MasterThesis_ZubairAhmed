##########################################################################################
# Version: M-2016.12-SP4 (July 17, 2017)
# Copyright (C) 2010-2017 Synopsys, Inc. All rights reserved.
##########################################################################################
puts "RM-Info: Running script [info script]\n"

# ELMOS
# source -echo ./rm_setup/icc_setup.tcl 

############################################################
## clock_opt_ccd_icc: Concurrent Clock and Data Optimization
############################################################
 
open_mw_lib $MW_DESIGN_LIBRARY
redirect /dev/null "remove_mw_cel -version_kept 0 ${ICC_CLOCK_OPT_CCD_CEL}" 
copy_mw_cel -from $ICC_PLACE_OPT_CEL -to $ICC_CLOCK_OPT_CCD_CEL
open_mw_cel $ICC_CLOCK_OPT_CCD_CEL



## Optimization Common Session Options - set in all sessions
source -echo common_optimization_settings_icc.tcl
source -echo common_placement_settings_icc.tcl

## Source CTS Options 
source -echo common_cts_settings_icc.tcl

## Source Post CTS Options
source -echo common_post_cts_timing_settings.tcl

##Source Concurrent Clock and Data Options
source -echo common_concurrent_clock_and_data_settings_icc.tcl

set_app_var compile_instance_name_prefix icc_ccd



   if {$ICC_MCMM_CLOCK_OPT_CCD_SCENARIOS != ""} {
       set_active_scenarios $ICC_MCMM_CLOCK_OPT_CCD_SCENARIOS
   } else {
       set_active_scenarios [lminus [all_scenarios] [get_scenarios -setup false -hold false -cts_mode true]]
       puts "RM-Info: CTS only scenarios (get_scenarios -setup false -hold false -cts_mode true) are made inactive by RM during CCD optimizations"
   }

   if { [llength [get_scenarios -cts_mode true -setup true -active true]] < 1 } {
      puts "RM-Error: You need to have at least one (timing critical) scenario as cts_mode=true and setup=true"
   }

if { [check_error -verbose] != 0} { echo "RM-Error, flagging ..." }

if {$ICC_AOCV_SCENARIO_MAPPING != "" || [file exists  [which $ICC_IN_AOCV_TABLE_FILE]]} {
  # Enable AOCV analysis
  set_app_var timing_aocvm_enable_analysis true
  set_app_var timing_aocvm_enable_distance_analysis true

  ## For when scenario specific AOCV data is to be applied
  if {$timing_library_derate_is_scenario_specific} {
    set cur_scenario [current_scenario]
    foreach pair $ICC_AOCV_SCENARIO_MAPPING {
      if {[file exists [which [lindex $pair 1] ] ]} {
        current_scenario [lindex $pair 0]
        read_aocvm [lindex $pair 1]
        # Report specified AOCV data and computed derates for the scenario
        redirect -append $REPORTS_DIR_CLOCK_OPT_CCD/$ICC_CLOCK_OPT_PSYN_CEL.aocvm.rpt {current_scenario; report_ocvm -type aocvm -nosplit}
      } else {
        echo "Error: Could not find the AOCV table file [lindex $pair 1] for the scenario [lindex $pair 0]"
      }
    }
    current_scenario $cur_scenario
  } else {
  ## If the AOCV data is not scenario specific 
    if {[file exists  [which $ICC_IN_AOCV_TABLE_FILE]]} {
      # Read AOCV tables for design, hierarchical cells or lib cells
      read_aocvm $ICC_IN_AOCV_TABLE_FILE
   
      # Report specified AOCV data and computed derates
      redirect -file $REPORTS_DIR_CLOCK_OPT_CCD/$ICC_CLOCK_OPT_PSYN_CEL.aocvm.rpt {report_ocvm -type aocvm -nosplit}
    }
  }
}


##############################
## RP : Relative Placement  ##                
##############################
## Ensuring that the RP cells are not changed during clock_opt
#set_rp_group_options [all_rp_groups] -cts_option fixed_placement
#set_rp_group_options [all_rp_groups] -cts_option "size_only"

# set_delay_calculation_options -routed_clock arnoldi

if {$ICC_SANITY_CHECK} {
        check_physical_design -stage pre_clock_opt -no_display -output $REPORTS_DIR_CLOCK_OPT_CCD/check_physical_design.pre_clock_opt 
}
if { [check_error -verbose] != 0} { echo "RM-Error, flagging ..." }

if {$ICC_ENABLE_CHECKPOINT} {
echo "RM-Info : Please ensure there's enough disk space before enabling the set_checkpoint_strategy feature."
set_checkpoint_strategy -enable -overwrite
# The -overwrite option is used by default. Remove it if needed.
}
# A SAIF file is optional for self-gating
if {$ICC_CTS_SELF_GATING && [file exists [which $ICC_IN_SAIF_FILE]]} {
  foreach scenario [all_active_scenarios] {
    current_scenario $scenario
    read_saif -input $ICC_IN_SAIF_FILE -instance_name $ICC_SAIF_INSTANCE_NAME
  }
}
   set cur_active_scenarios [all_active_scenarios]
   set_active_scenarios -all
   foreach scenario [all_active_scenarios] {
     current_scenario $scenario
     # remove ideal network
     remove_ideal_network [all_fanout -flat -clock_tree]
   }
   set_active_scenarios $cur_active_scenarios

   foreach scenario [all_active_scenarios] {
     current_scenario $scenario
     #set fix hold
     set_fix_hold [all_clocks]

     #uncertainties
     if {$ICC_APPLY_RM_UNCERTAINTY_POSTCTS && [file exists [which $ICC_UNCERTAINTY_POSTCTS_FILE.$scenario]] } {
       echo "RM-Info: Sourcing the post-cts uncertainty file : [which $ICC_UNCERTAINTY_POSTCTS_FILE.$scenario]"
       source -echo $ICC_UNCERTAINTY_POSTCTS_FILE.$scenario
     }
   }


# Controls the effort level of TNS optimization
set_optimization_strategy -tns_effort $ICC_TNS_EFFORT_PREROUTE

if {[file exists [which $CUSTOM_CLOCK_OPT_CCD_PRE_SCRIPT]]} {
echo "RM-Info: Sourcing [which $CUSTOM_CLOCK_OPT_CCD_PRE_SCRIPT]"
source $CUSTOM_CLOCK_OPT_CCD_PRE_SCRIPT
}

# Setup CCD commands to perform timing driven clock tree and post-CTS CCD
set clock_opt_ccd_cmd1 "clock_opt -concurrent_clock_and_data -only_cts -no_clock_route -area_recovery "
set clock_opt_ccd_cmd2 "clock_opt -concurrent_clock_and_data -only_psyn -no_clock_route -area_recovery "
set clock_opt_ccd_cmd3 "clock_opt -incremental_concurrent_clock_and_data -no_clock_route -area_recovery "

if {$ICC_CTS_INTERCLOCK_BALANCING && [file exists [which $ICC_CTS_INTERCLOCK_BALANCING_OPTIONS_FILE]]} {
lappend clock_opt_ccd_cmd1 -inter_clock_balance
}
if {$ICC_CTS_UPDATE_LATENCY} {
lappend clock_opt_ccd_cmd1 -update_clock_latency
}

if {!$DFT && [get_scan_chain] == 0} {
lappend clock_opt_ccd_cmd1 -continue_on_missing_scandef
lappend clock_opt_ccd_cmd2 -continue_on_missing_scandef
lappend clock_opt_ccd_cmd3 -continue_on_missing_scandef
}
if {$PLACE_OPT_CONGESTION_DRIVEN} {
lappend clock_opt_ccd_cmd1 -congestion
lappend clock_opt_ccd_cmd2 -congestion
}
if {$POWER_OPTIMIZATION} {
lappend clock_opt_ccd_cmd1 -power
lappend clock_opt_ccd_cmd2 -power
}
## Use -optimize_dft if you have SCANDEF and there are scan nets with hold violations.
#  Note that scan wirelength can increase and may impact QoR.

## concurrent clock and data optimization command
## The timing critical scenario has to be set as current_secenario before calling concurrent clock and data optimization command 
   if {$ICC_MCMM_CLOCK_OPT_CCD_TIMING_CRITICAL_SCENARIO != ""} {
      if {[lsearch -inline [get_scenarios -cts_mode true -setup true -active true] $ICC_MCMM_CLOCK_OPT_CCD_TIMING_CRITICAL_SCENARIO] != $ICC_MCMM_CLOCK_OPT_CCD_TIMING_CRITICAL_SCENARIO} {
         puts "RM-Error : Timing Critical Scenario $ICC_MCMM_CLOCK_OPT_CCD_TIMING_CRITICAL_SCENARIO is invalid. It is not cts_mode=true && setup=true && active=true"
      } else {
      current_scenario $ICC_MCMM_CLOCK_OPT_CCD_TIMING_CRITICAL_SCENARIO
      }
   } else {
      puts "RM-Error: The variable ICC_MCMM_CLOCK_OPT_CCD_TIMING_CRITICAL_SCENARIO is not set. It is mandatory to specify this variable"
   }
echo $clock_opt_ccd_cmd1
eval $clock_opt_ccd_cmd1

# Do not change timing analysis, extraction, optimization settings here.
save_mw_cel -as CCD_intermediate
extract_rc
report_qor

   if {$ICC_MCMM_CLOCK_OPT_CCD_TIMING_CRITICAL_SCENARIO != ""} {
      if {[lsearch -inline [get_scenarios -cts_mode true -setup true -active true] $ICC_MCMM_CLOCK_OPT_CCD_TIMING_CRITICAL_SCENARIO] != $ICC_MCMM_CLOCK_OPT_CCD_TIMING_CRITICAL_SCENARIO} {
         puts "RM-Error : Timing Critical Scenario $ICC_MCMM_CLOCK_OPT_CCD_TIMING_CRITICAL_SCENARIO is invalid. It is not cts_mode=true && setup=true && active=true"
      } else {
      current_scenario $ICC_MCMM_CLOCK_OPT_CCD_TIMING_CRITICAL_SCENARIO
      }
   } else {
      puts "RM-Error: The variable ICC_MCMM_CLOCK_OPT_CCD_TIMING_CRITICAL_SCENARIO is not set. It is mandatory to specify this variable"
   }
echo $clock_opt_ccd_cmd2
eval $clock_opt_ccd_cmd2

# Do not change timing analysis, extraction, optimization settings here.
extract_rc
report_qor

# Check the effort setting in CCD strategy and run standalone incremental CCD only in high effort.
if {$ICC_CLOCK_OPT_CCD_EFFORT == "HIGH"} {
  echo "RM-Info: Flow effort is set to high. Running Incremental CCD as a separate step."
  echo $clock_opt_ccd_cmd3
  eval $clock_opt_ccd_cmd3
} elseif {$ICC_CLOCK_OPT_CCD_EFFORT == "MEDIUM"} {
  echo "RM-Info: Flow effort is set to medium. Incremental CCD was already run in clock_opt -only_psyn -concurrent_clock_and_data step. Skip running it standalone"
}

extract_rc
report_qor

if {[file exists [which $CUSTOM_CLOCK_OPT_CCD_POST_SCRIPT]]} {
echo "RM-Info: Sourcing [which $CUSTOM_CLOCK_OPT_CCD_POST_SCRIPT]"
source $CUSTOM_CLOCK_OPT_CCD_POST_SCRIPT
}

if {$ICC_ENABLE_CHECKPOINT} {set_checkpoint_strategy -disable}

route_zrt_group -all_clock_nets -reuse_existing_global_route true -stop_after_global_route true
if { [check_error -verbose] != 0} { echo "RM-Error, flagging ..." }

############################################################################################################
# ADDING ADDITIONAL FEATURES FOR TIMING OPTIMIZATION
############################################################################################################

## When the design has congestion issues post CTS, use :
# refine_placement -congestion_effort medium

## Additional optimization can be done using the psynopt command
# psynopt -effort "medium|high"

## checking whether the clock nets got the NDR
# report_net_routing_rules [get_nets -hier *]

if {$CLOCK_OPT_PSYN_PREROUTE_FOCALOPT_LAYER_OPTIMIZATION} {
## For advanced technologies, where upper metal layer resistance values are much smaller then lower layer ones,
#  you can perform layer optimization to improve existing buffer trees.
#  Use set_preroute_focal_opt_strategy to customize the settings.
report_preroute_focal_opt_strategy
preroute_focal_opt -layer_optimization
}

########################################
#         ANTENNA PREVENTION           #
########################################

if {$ICC_USE_DIODES && $ICC_PORT_PROTECTION_DIODE != ""} {
 ## Optionally insert a diode before routing to avoid antenna's on the ports of the block
 remove_attribute $ICC_PORT_PROTECTION_DIODE dont_use
 set ports [remove_from_collection [get_ports * -filter "direction==in"] [get_ports $ICC_PORT_PROTECTION_DIODE_EXCLUDE_PORTS]]
 insert_port_protection_diodes -prefix port_protection_diode -diode_cell [get_lib_cells $ICC_PORT_PROTECTION_DIODE] -port $ports -ignore_dont_touch
 legalize_placement
 
}


########################################
#           CONNECT P/G                #
########################################
## Connect Power & Ground for non-MV and MV-mode

 if {[file exists [which $CUSTOM_CONNECT_PG_NETS_SCRIPT]]} {
   echo "RM-Info: Sourcing [which $CUSTOM_CONNECT_PG_NETS_SCRIPT]"
   source -echo $CUSTOM_CONNECT_PG_NETS_SCRIPT
 } else {
    derive_pg_connection -power_net $MW_POWER_NET -power_pin $MW_POWER_PORT -ground_net $MW_GROUND_NET -ground_pin $MW_GROUND_PORT 
    if {!$ICC_TIE_CELL_FLOW} {derive_pg_connection -power_net $MW_POWER_NET -ground_net $MW_GROUND_NET -tie}
   }
if { [check_error -verbose] != 0} { echo "RM-Error, flagging ..." }

save_mw_cel -as $ICC_CLOCK_OPT_CCD_CEL

if {$ICC_REPORTING_EFFORT == "MED" } {
 redirect -tee -file $REPORTS_DIR_CLOCK_OPT_CCD/$ICC_CLOCK_OPT_CCD_CEL.qor {report_qor}
 redirect -tee -file $REPORTS_DIR_CLOCK_OPT_CCD/$ICC_CLOCK_OPT_CCD_CEL.qor -append {report_qor -summary}
 # redirect -tee -file $REPORTS_DIR_PLACE_OPT/$ICC_CLOCK_OPT_CCD_CEL.qor -append {report_timing_histogram -range_maximum 0 -scenario [all_active_scenarios]}
 # redirect -tee -file $REPORTS_DIR_PLACE_OPT/$ICC_CLOCK_OPT_CCD_CEL.qor -append {report_timing_histogram -range_minimum 0 -scenario [all_active_scenarios]}
 redirect -file $REPORTS_DIR_CLOCK_OPT_CCD/$ICC_CLOCK_OPT_CCD_CEL.con {report_constraints}
 redirect -file $REPORTS_DIR_CLOCK_OPT_CCD/$ICC_CLOCK_OPT_CCD_CEL.placement_utilization.rpt {report_placement_utilization -verbose}
}


if {$ICC_REPORTING_EFFORT != "OFF" } {
     if {[llength [get_scenarios -active true -setup true]]} {
     redirect -file $REPORTS_DIR_CLOCK_OPT_CCD/$ICC_CLOCK_OPT_CCD_CEL.clock_timing {report_clock_timing -nosplit -type skew -scenarios [get_scenarios -active true -setup true]} ;# local skew report
     redirect -tee -file $REPORTS_DIR_CLOCK_OPT_CCD/$ICC_CLOCK_OPT_CCD_CEL.max.clock_tree {report_clock_tree -nosplit -summary -scenarios [get_scenarios -active true -setup true]}     ;# global skew report
     }
     if {[llength [get_scenarios -active true -hold true]]} {
     redirect -tee -file $REPORTS_DIR_CLOCK_OPT_CCD/$ICC_CLOCK_OPT_CCD_CEL.min.clock_tree {report_clock_tree -nosplit -operating_condition min -summary -scenarios [get_scenarios -active true -hold true]}     ;# min global skew report
     }
}
if {$ICC_REPORTING_EFFORT != "OFF" } {
 redirect -file $REPORTS_DIR_CLOCK_OPT_CCD/$ICC_CLOCK_OPT_CCD_CEL.max.tim {report_timing -nosplit -scenario [all_active_scenarios] -capacitance -transition_time -input_pins -nets -delay max} 
 redirect -file $REPORTS_DIR_CLOCK_OPT_CCD/$ICC_CLOCK_OPT_CCD_CEL.min.tim {report_timing -nosplit -scenario [all_active_scenarios] -capacitance -transition_time -input_pins -nets -delay min} 
}
if {$ICC_REPORTING_EFFORT == "MED" && $POWER_OPTIMIZATION } {
 redirect -file $REPORTS_DIR_CLOCK_OPT_CCD/$ICC_CLOCK_OPT_CCD_CEL.power {report_power -nosplit -scenario [all_active_scenarios]}
}

## Create Snapshot and Save
if {$ICC_REPORTING_EFFORT != "OFF" } {
   redirect -file $REPORTS_DIR_CLOCK_OPT_CCD/$ICC_CLOCK_OPT_CCD_CEL.placement_utilization.rpt {report_placement_utilization -verbose}
   create_qor_snapshot -clock_tree -name $ICC_CLOCK_OPT_CCD_CEL
   redirect -file $REPORTS_DIR_CLOCK_OPT_CCD/$ICC_CLOCK_OPT_CCD_CEL.qor_snapshot.rpt {report_qor_snapshot -no_display}
}

## Categorized Timing Report (CTR)
#  Use CTR in the interactive mode to view the results of create_qor_snapshot. 
#  Recommended to be used with GUI opened.
#  query_qor_snapshot -display (or GUI: Timing -> Query QoR Snapshot)
#  query_qor_snapshot condenses the timing report into a cross-referencing table for quick analysis. 
#  It can be used to highlight violating paths and metric in the layout window and timing reports. 
#  CTR also provides special options to focus on top-level and hierarchical timing issues. 
#  When dealing with dirty designs, increasing the number violations per path to 20-30 when generating a snapshot can help 
#  find more issues after each run (create_qor_snapshot -max_paths 20).
#  Specify -type min for hold time violations. 

puts "RM-Info: Completed script [info script]\n"

# ELMOS: removed, leave it to the main script if we want to exit the tool here
#exit

