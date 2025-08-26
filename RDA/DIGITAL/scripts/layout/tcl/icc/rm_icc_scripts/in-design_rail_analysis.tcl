##########################################################################
# In-Design Rail Analysis Reference Methodology 
# Version: M-2016.12-SP4 (July 17, 2017)
# Copyright (C) 2010-2017 Synopsys, Inc. All rights reserved.
##########################################################################

puts "RM-Info: Running script [info script]\n"

source -echo ./rm_setup/icc_setup.tcl 

#######################################
####PrimeRail Analysis Script
#######################################

##Open Design
open_mw_lib $MW_DESIGN_LIBRARY

open_mw_cel $PRIMERAIL_ANALYSIS_INPUT_CEL

##################################################################
#    PG Net RC extraction                                        #
##################################################################

if { [file exists $TLUPLUS_MAX_FILE] && [file exists $MAP_FILE] } {
   set_tlu_plus_files \
      -max_tluplus $TLUPLUS_MAX_FILE \
      -min_tluplus $TLUPLUS_MIN_FILE \
      -tech2itf_map $MAP_FILE \
} else {
   echo "SCRIPT-Error: TLUPlus and/or MAP files for PG Extraction are not specified or found.  Please investigate."
   exit
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





#######################################
#### Set Rail Options
#######################################



if {$PRIMERAIL_DIR == ""} {
  set PRIMERAIL_DIR [file dirname [sh which pr_shell]]
}

if {[which $PRIMERAIL_DIR/pr_shell] == "" } {
  echo "RM-Error: Unable to find pr_shell at \"$PRIMERAIL_DIR\". Exiting...."
  exit
}



set_rail_options -default 
set_rail_options -use_pins_as_pads  $PRIMERAIL_USE_PINS_AS_PADS 

if { $PRIMERAIL_OPERATING_CONDITIONS != ""} {
   set_operating_conditions $PRIMERAIL_OPERATING_CONDITIONS
}

if {[file exists [which $PRIMERAIL_PAD_INSTANCE_FILE]]} {
   set_rail_options -pad_instance_file $PRIMERAIL_PAD_INSTANCE_FILE 
} elseif {[file exists [which $PRIMERAIL_PAD_MASTER_FILE]]} {
   set_rail_options -pad_master_file $PRIMERAIL_PAD_MASTER_FILE
}

set_rail_options \
    -pr_exec_dir $PRIMERAIL_DIR \
    -output_dir  $PRIMERAIL_WORK_DIR 

if {[file exists [which $PRIMERAIL_SDC_FILE]]} {
   set_rail_options -sdc $PRIMERAIL_SDC_FILE 
}
if {[file exists [which $PRIMERAIL_SPEF_FILE]]} {
   set_rail_options -spef $PRIMERAIL_SPEF_FILE 
}

# Set the analysis mode for analyze_rail
set_rail_options -analysis_mode $PRIMERAIL_ANALYSIS_MODE

if {$PRIMERAIL_ANALYSIS_MODE == "dynamic"} {
   if {[lindex $PRIMERAIL_SWITCHING_ACTIVITY_FILE 0] == "vcd" && [file exists [which [lindex $PRIMERAIL_SWITCHING_ACTIVITY_FILE 1]]]} {
      set_rail_options -switching_activity $PRIMERAIL_SWITCHING_ACTIVITY_FILE 
   } else {
      echo "RM-Info: Error: A VCD file is required for dynamic analysis mode"
   }
} else {
   if {[file exists [which [lindex $PRIMERAIL_SWITCHING_ACTIVITY_FILE 1]]]} {
      set_rail_options -switching_activity $PRIMERAIL_SWITCHING_ACTIVITY_FILE 
   }
}

if {[file exists [which $PRIMERAIL_PACKAGING_FILE]]} {
   set_rail_options -packaging_file $PRIMERAIL_PACKAGING_FILE
}
if {[file exists [which $PRIMERAIL_CONFIG_FILE]]} {
   set_rail_options -config_file $PRIMERAIL_CONFIG_FILE
}

if {$PRIMERAIL_HOST_MACHINE != ""} {
   set_rail_options -host $PRIMERAIL_HOST_MACHINE
}
if {$PRIMERAIL_VD_THRESHOLD != ""} {
   set_rail_options -vd_threshold $PRIMERAIL_VD_THRESHOLD
}

if {$PRIMERAIL_SIGNAL_PARASITICS_FORMAT == "SPEF"} {
   set_rail_options -signal_parasitics_output_format $PRIMERAIL_SIGNAL_PARASITICS_FORMAT
}

if {$PRIMERAIL_POWER_SCALE_VALUE != ""} {
  set_rail_options -power_scale_value $PRIMERAIL_POWER_SCALE_VALUE
  } elseif {$PRIMERAIL_POWER_SCALE_FACTOR != ""} {
  set_rail_options -power_scale_factor $PRIMERAIL_POWER_SCALE_FACTOR
}

if {$PRIMERAIL_ANALYSIS_MODE != "static"} {
  if {$PRIMERAIL_ANALYSIS_START_TIME != ""} {
     set_rail_options -start_time $PRIMERAIL_ANALYSIS_START_TIME
  }

  if {$PRIMERAIL_ANALYSIS_END_TIME != ""} {
     set_rail_options -end_time $PRIMERAIL_ANALYSIS_END_TIME
  }
}

if {$PRIMERAIL_WRITE_RAIL_DATA != ""} {
  set_rail_options -write_rail_data $PRIMERAIL_WRITE_RAIL_DATA
}

if {$PRIMERAIL_VIA_ARRAY_PARTITION_SIZE != ""} {
  set_rail_options -via_array_partition_size $PRIMERAIL_VIA_ARRAY_PARTITION_SIZE 
} 

set rail_reuse ""

if {$PRIMERAIL_REUSE_POWER == "TRUE"} {
  lappend rail_reuse power 
}

if {$PRIMERAIL_REUSE_PG_EXTRACTION == "TRUE"} {
  lappend rail_reuse pg_extraction
}

if {$PRIMERAIL_REUSE_SETUP_VARIABLES == "TRUE"} {
  lappend rail_reuse setup_variables
}

if {$PRIMERAIL_REUSE_SETUP_FILES == "TRUE"} {
  lappend rail_reuse setup_files
}

if {$PRIMERAIL_REUSE_SIGNAL_EXTRACTION == "TRUE"} {
  lappend rail_reuse signal_extraction
}

if {$rail_reuse != ""} {
  set_rail_options -reuse $rail_reuse
}

if {$PRIMERAIL_ASSIGN_POWER == "TRUE" && $PRIMERAIL_REUSE_POWER != "TRUE"} {
  set_rail_options -assign_power_only TRUE
}
   


redirect -tee -file $REPORTS_DIR_IN_DESIGN_RAIL/prime_rail_options.rpt {report_rail_options}



#############################################################
## START In-Design Analysis  			   ##
#############################################################
echo "RM-Info: starting the ICC-PrimeRail analysis flow ... "

if {[file exists [which $PRIMERAIL_ANALYSIS_CUSTOM_SCRIPT  ]]} {
        analyze_rail -primerail_script_file $PRIMERAIL_ANALYSIS_CUSTOM_SCRIPT
} else {
    if {$PRIMERAIL_ANALYSIS_EM == "TRUE" || $PRIMERAIL_ANALYSIS_INTEGRITY == "TRUE" || $PRIMERAIL_ANALYSIS_RAIL == "TRUE" || $PRIMERAIL_SCRIPT_ONLY == "TRUE"} {
       set rail_cmd  "analyze_rail "
       set rail_nets $PRIMERAIL_ANALYSIS_NETS
  if {$PRIMERAIL_ANALYSIS_EM eq "TRUE" }	 {
       lappend rail_cmd -electromigration  }
        if {$PRIMERAIL_ANALYSIS_RAIL eq "TRUE" }   {
             lappend rail_cmd -voltage_drop  }
        if {$PRIMERAIL_ANALYSIS_INTEGRITY eq "TRUE" }   {
             lappend rail_cmd -integrity  }
        if {$PRIMERAIL_SCRIPT_ONLY eq "TRUE" }   {
             lappend rail_cmd -script_only } 
             echo "RM-Info: Executing  ${rail_cmd} \{${rail_nets}\}"
eval ${rail_cmd} {${rail_nets}}

    } else {
       echo "RM-Info: Error! Please configure to use custom script or one of EM|IR drop|Integrity check"
  #analyze_rail -what ?
    }
  }

puts "RM-Info: Completed script [info script]\n"

exit

