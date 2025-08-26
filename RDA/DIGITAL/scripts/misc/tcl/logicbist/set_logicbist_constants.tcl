# (c) 2019 Synopsys, Inc.  All rights reserved.             
#                                                                  
# This script is proprietary and confidential information of        
# Synopsys, Inc. and may be used and disclosed only as authorized   
# per your agreement with Synopsys, Inc. controlling such use and   
# disclosure.                                                       


# set_logicbist_constants.tcl - sets LogicBIST seed, signature, pattern count constant values
#
# v1.0  chrispy  07/02/2015
#  initial release
# v1.1  chrispy  07/07/2015
#  support nondefault compile_instance_name_prefix values
# v1.2  chrispy  11/13/2015
#  use/report non-reversed values instead
#  remove -zero_values option
# v1.3  chrispy  08/02/2017
#  add support for forcing port-driven values
#  add -force_shift_counter
# v1.4  acron    09/06/2017
#  add -write_1500 to write IEEE 1500 testbench for CDR-driven values
#  rename -output to -write_vcs
#  add better UI checking (mutually exclusive, required-together options)
# v2.0  chrispy  11/13/2017
#  add support for hierarchical IEEE 1500 flows
#  add support for IC Compiler and IC Compiler II
#  add -dont_touch option to preserve constants through optimization
#  added proper DUT prefix to -write_vcs output
# v2.1  chrispy  01/18/2018
#  fix typo in VCS force file
# v2.2  chrispy  05/23/2018
#  add support for stuck-at, transition patterns in IEEE 1500 flows (O-2018.06 or later required)
# v2.3  chrispy  06/04/2019
#  add "run" to end of VCS command file


proc _LB_get_parent_cell_name {cell} {
 return [string range [get_object_name $cell] 0 end-[string length [get_attribute $cell name]]]
}
define_proc_attributes _LB_get_parent_cell_name -hide_body -hidden -dont_abbrev

proc _LB_toBinaryString {val} {
 #echo [expr $val -9]
 set result [expr {($val==0)?0:""}]
 while { $val != 0 } {
	set result "[expr {($val&1)?1:0}]${result}"
	set val [expr {$val>>1}]
 }
 return $result
}
define_proc_attributes _LB_toBinaryString -hide_body -hidden -dont_abbrev

proc _LB_get_STIL_values {file_name} {
 # this ordering ensures we get the FIRST PRPG and the LAST pattern counter
 set STIL_file [open $file_name]
 set state 0
 set clock_cycles 1
 while {[gets $STIL_file line] != -1} {
  switch $state {
   0 {
    if {[regexp "^ +Ann .. LBIST careprpg_seed .* reversed (\[01\]+) " $line dummy PRPG_seed]} {
     set state 1
    }
   }
   1 {
    if {[string first {Ann {* fast_sequential *}} $line] != -1} {set clock_cycles 2}
    if {[regexp "^ +Ann .. LBIST pattern_counter (\[0-9\]+) shift_counter (\[0-9\]+) " $line dummy pattern_counter shift_counter]} {
     set state 2
    }
   }
   2 {
    if {[regexp "^ +Ann .. LBIST misr .* reversed (\[01\]+) " $line dummy MISR_signature]} {
     set state 3
     break
    }
   }
  }
 }
 close $STIL_file

 switch $state {
  0 {error {Could not find PRPG value in STIL file.}}
  1 {error {Could not find pattern counter value in STIL file.}}
  2 {error {Could not find MISR value in STIL file.}}
 }

 incr pattern_counter ;# account for initializing load with no unload
 return [list [_LB_toBinaryString $shift_counter] [_LB_toBinaryString $pattern_counter] $PRPG_seed $MISR_signature $clock_cycles]
}
define_proc_attributes _LB_get_STIL_values -hide_body -hidden -dont_abbrev

proc _LB_connect_to_value {pin val} {
 set hier_prefix [_LB_get_parent_cell_name [get_cells -of $pin]]
 if {[get_nets -quiet ${hier_prefix}nLogicBIST_Logic${val}] eq {}} {
  switch $::synopsys_program_name {
   dc_shell {
    redirect /dev/null {
     create_cell -logic $val ${hier_prefix}LogicBIST_Logic${val}
     create_net ${hier_prefix}nLogicBIST_Logic${val}
     connect_net ${hier_prefix}nLogicBIST_Logic${val} ${hier_prefix}LogicBIST_Logic${val}/**logic_${val}**
    }
   }
   icc_shell -
   icc2_shell {
    redirect /dev/null {
     create_net ${hier_prefix}nLogicBIST_Logic${val} {*}[expr {${val} ? {-tie_high} : {-tie_low}}]
    }
   }
  }
 }

# echo "  Connecting $pin to logic $val"
 redirect /dev/null {
  disconnect_net [get_nets -of_objects $pin] $pin
  connect_net ${hier_prefix}nLogicBIST_Logic${val} $pin
 }
}
define_proc_attributes _LB_connect_to_value -hide_body -hidden -dont_abbrev

proc _LB_get_pin_value {pin} {
 switch $::synopsys_program_name {
  dc_shell {
   redirect /dev/null {
    set fanin [all_fanin -flat -start -to $pin]
   }
   if {[sizeof_collection $fanin] != 1 || [set this_val [get_attribute -quiet $fanin constant_value]] eq {}} {
    return "Pin '$pin' IS NOT driven by a single constant pin."
   }
   return $this_val
  }
  icc_shell {
   set net [add_to_collection -unique [get_nets -quiet -of $pin] [get_flat_nets -quiet -of $pin]]
   if {[filter_collection $net {is_tie_low_net == true}] ne {}} {
    return 0
   } elseif {[filter_collection $net {is_tie_high_net == true}] ne {}} {
    return 1
   }
   redirect /dev/null {
    set fanin [all_fanin -flat -start -to $pin]
   }
   if {[sizeof_collection $fanin] != 1 || [set this_val [get_attribute -quiet $fanin constant_value]] eq {}} {
    return "Pin '$pin' IS NOT driven by a single constant pin or net."
   }
   return $this_val
  }
  icc2_shell {
   set net [add_to_collection -unique [get_nets -quiet -of $pin] [get_flat_nets -quiet -of $pin]]
   if {[filter_collection $net {has_ground == true || has_logic_zero == true || has_low == true}] ne {}} {
    return 0
   } elseif {[filter_collection $net {has_power == true || has_logic_one == true || has_high == true}] ne {}} {
    return 1
   }
   redirect /dev/null {
    set fanin [all_fanin -flat -start -to $pin]
   }
   if {[sizeof_collection $fanin] != 1 || [set this_val [get_attribute -quiet $fanin constant_value]] eq {}} {
    return "Pin '$pin' IS NOT driven by a single constant pin or net."
   }
   return $this_val
  }
 }
}
define_proc_attributes _LB_get_pin_value -hide_body -hidden -dont_abbrev

proc _LB_check_value {pin val} {
 set this_val [_LB_get_pin_value $pin]
 if {[string length $this_val] > 1} {
  echo "  $this_val"
  return 1
 } elseif {$this_val ne $val} {
  echo "  Pin '$pin' IS NOT set to logic $val."
  return 1
 } else {
  echo "  Verified $pin is set to logic $val"
  return 0
 }
}
define_proc_attributes _LB_check_value -hide_body -hidden -dont_abbrev

proc _LB_report_value {pin} {
 set this_val [_LB_get_pin_value $pin]
 if {[string length $this_val] > 1} {
  error $this_val
 }
 return $this_val
}
define_proc_attributes _LB_report_value -hide_body -hidden -dont_abbrev

proc _LB_eco_connect_signals { name pins word operation } {
 upvar results results
 upvar current_design current_design
 if {[info exists results(-write_1500)]} {
  echo "Setting $name value to '$word' in STIL testbench...\n"
  return
 }

 redirect /dev/null {set fi [all_fanin -flat -start -trace all -to $pins]}  ;# icc2 makes noise
 if {[get_ports -quiet $fi] eq {} && [get_cells -quiet -of $fi -filter {is_sequential == true}] eq {}} {
  # no ports or registers; netlist constant drivers only
  switch $operation {
   connect {
    echo "Setting $name value to '$word' in netlist..."
    foreach pin [lsort -dictionary -decreasing [get_object_name $pins]] value [split $word {}] {
     _LB_connect_to_value $pin $value
    }
   }
   check {
    echo "Verifying $name value is set to '$word' in netlist..."
    set wrong_connections 0
    foreach pin [lsort -dictionary -decreasing [get_object_name $pins]] value [split $word {}] {
     incr wrong_connections [_LB_check_value $pin $value]
    }
    if {$wrong_connections > 0} {error {One or more signal connections have unexpected values.}}
   }
   report {
    echo "Reporting $name value..."
    foreach pin [lsort -dictionary -decreasing [get_object_name $pins]] {
     append word [_LB_report_value $pin]
    }
    echo "  Determined $name value is set to '$word'."
   }
  }
 } else {
  # look for a single unique port (no more, no less) in fanin to each pin
  array unset port_count
  foreach_in_collection pin $pins {
   set pin_name [get_object_name $pin]
   set fi_ports($pin_name) [get_ports -quiet [all_fanin -flat -start -to $pin -trace all]]
   foreach_in_collection port $fi_ports($pin_name) {
    incr port_count([get_object_name $port])
   }
  }
  foreach port [array names port_count] {
   if {$port_count($port) == 1} {unset port_count($port)}
  }
  set common_ports [get_ports -quiet [array names port_count]]
  set wrong_port 0
  foreach_in_collection pin $pins {
   set pin_name [get_object_name $pin]
   set port [remove_from_collection $fi_ports($pin_name) $common_ports]
   if {[sizeof_collection $port] == 1} {
    set port_for_pin($pin_name) $port
   } else {
    if {$port eq {}} {
     echo "'$pin_name' has no unique ports upstream."
    } else {
     echo "'$pin_name' has too many unique ports upstream: {[get_object_name $port]}"
    }
    incr wrong_port
   }
  }
  if {$wrong_port > 0} {error {One or more signal connections do not have single unique ports driving them.}}

  switch $operation {
   connect -
   check {
    if {![info exists results(-write_vcs)]} {error "VCS command file not specified with -write_vcs option"}
    echo "Forcing $name value to '$word' in VCS command file '$results(-write_vcs)'..."
    redirect -append $results(-write_vcs) {
     echo "# Forcing $name value to '$word'..."
     foreach pin [lsort -dictionary -decreasing [get_object_name $pins]] value [split $word {}] {
      regsub -all {([\[\]])} [get_object_name $port_for_pin($pin)] {\\\1} port_name
      echo "force ${current_design}_test.dut.${port_name} 1'b$value"
     }
     echo "run"
    }
   }
   report {
    echo "Reporting $name value..."
    echo "  Signal is port-driven, no netlist value to report."
   }
  }
 }
 echo ""
}
define_proc_attributes _LB_eco_connect_signals -hide_body -hidden -dont_abbrev

proc set_logicbist_constants {args} {
 set results(-force_shift_counter) 0
 parse_proc_arguments -args $args results

 # tool validation
 if {$::synopsys_program_name ne {dc_shell}} {
  if {[info exists results(-write_1500)]} {error {The -write_1500 option is supported only in Design Compiler.}}
 }

 # are we reporting the values?
 set report [expr {![info exists results(-file_name)]}]

 # use this to track any errors we've hit
 set err {}

 # get current design name
 redirect /dev/null {set current_design [get_object_name [current_design]]}

 # make sure we can find one BIST controller that matches the current design name
 set bist_controller [get_cells -hierarchical -quiet "${current_design}_U_LogicBISTController_*"]
 if {$bist_controller eq {}} {
  set bist_controller [get_cells -hierarchical -quiet "*_${current_design}_U_LogicBISTController_*"]
 }
 if {$bist_controller eq {}} {
  set bist_controller [get_cells -hierarchical -quiet "*_U_LogicBISTController_*"]  ;# look for it inside a DFT-inserted core
 }
 if {$bist_controller eq {}} {
  lappend err "No LogicBIST controller found."
 } elseif {[sizeof_collection $bist_controller] > 1} {
  lappend err "Multiple LogicBIST controllers are not supported."
 }

 # get test-mode name from instance name
 if {$bist_controller ne {}} {
  regexp {_LogicBISTController_(.*)} [get_object_name $bist_controller] dummy mode_name
  echo "Found LogicBIST controller for '$mode_name' test mode."
 }

 # verify decompressor and compressor are present
 if {[info exists mode_name] && $mode_name ne {}} {
  set decompressor [get_cells -quiet -hierarchical U_decompressor_${mode_name}]
  if {$decompressor eq {}} {
   set decompressor [get_cells -quiet -hierarchical *_U_decompressor_${mode_name}]
  }
  if {$decompressor eq {}} {
   lappend err "LogicBIST decompressor '${current_design}_U_decompressor_${mode_name}' not found."
  }

  set compressor [get_cells -quiet -hierarchical U_compressor_${mode_name}]
  if {$compressor eq {}} {
   set compressor [get_cells -quiet -hierarchical *_U_compressor_${mode_name}]
  }
  if {$compressor eq {}} {
   error "LogicBIST compressor '${current_design}_U_compressor_${mode_name}' not found."
  }
 }

 # verify that we can find all pins
 if {$bist_controller ne {}} {
  set shift_counter_pins [get_pins -quiet -of $bist_controller -filter {name =~ shift_count_data[*]}]
  set pattern_counter_pins [get_pins -quiet -of $bist_controller -filter {name =~ user_pattern_count_data[*]}]
  set PRPG_pins [get_pins -quiet -of $decompressor -filter {name =~ user_prpg_seed[*]}]
  set MISR_pins [get_pins -quiet -of $compressor -filter {name =~ user_misr_signature[*]}]
 }

 if {!$report} {
  # get data from STIL file
  foreach {shift_counter pattern_counter PRPG_seed MISR_signature clock_cycles} [_LB_get_STIL_values $results(-file_name)] {}
  echo "Obtained data from '$results(-file_name)' file."

  if {$bist_controller ne {}} {
   if {[sizeof_collection $PRPG_pins] != [string length $PRPG_seed]} {lappend err {PRPG length mismatch between design and STIL.}}
   if {[sizeof_collection $MISR_pins] != [string length $MISR_signature]} {lappend err {MISR length mismatch between design and STIL.}}
   if {[sizeof_collection $shift_counter_pins] < [string length $shift_counter]} {lappend err {Shift counter length in design is smaller than STIL value.}}
   if {[sizeof_collection $pattern_counter_pins] < [string length $pattern_counter]} {lappend err {Pattern counter length in design is smaller than STIL value.}}
  }

  # extend shift counter, pattern counter values as needed
  if {$err eq {}} {
   set shift_counter [string repeat 0 [expr {[sizeof_collection $shift_counter_pins]-[string length $shift_counter]}]]$shift_counter
   set pattern_counter [string repeat 0 [expr {[sizeof_collection $pattern_counter_pins]-[string length $pattern_counter]}]]$pattern_counter
  }
 } elseif {$report} {
  # the word values are unused when reporting the current values
  foreach var {shift_counter pattern_counter PRPG_seed MISR_signature} {set $var {}}
 }
 echo ""

 # verify all pins are loaded by logic (no constants pushed into logic)
 if {$bist_controller ne {}} {
  set pins {}
  append_to_collection pins $PRPG_pins
  append_to_collection pins $MISR_pins
  append_to_collection pins $shift_counter_pins
  append_to_collection pins $pattern_counter_pins
  set missing_connections 0
  foreach_in_collection pin $pins {
   redirect /dev/null {set fo [all_fanout -flat -endpoints_only -trace all -from $pin]}  ;# icc2 makes noise
   if {$fo eq {}} {
    lappend err "Hierarchical pin '[get_object_name $pin]' is unloaded due to constant optimization."
    if {![regexp {^shift_count_data} [get_attribute $pin name]]} {
     incr missing_connections
    }
   }
  }
  if {$missing_connections} {lappend err {One or more user signal connections have been optimized away.}}
 } else {
  # these values are unused when writing a 1500 test
  foreach var {shift_counter_pins pattern_counter_pins PRPG_pins MISR_pins} {set $var {}}
 }

 if {$err ne {}} {
  echo [join $err "\n"]
  if {![info exists results(-write_1500)]} {
   error {Unrecoverable errors encountered.}
  }
 }

 # connect/verify or report signals
 if {[info exists results(-dont_touch)]} {
  set bist_pins [list $PRPG_pins $MISR_pins $shift_counter_pins $pattern_counter_pins]
  switch $::synopsys_program_name {
   dc_shell {
    switch $results(-dont_touch) {
     true {
      echo "Applying 'set_compile_directives -constant_propagation false' to constant BIST pins."
      set_compile_directives -constant_propagation false $bist_pins
     }
     false {
      echo "Applying 'set_compile_directives -constant_propagation true' to constant BIST pins."
      set_compile_directives -constant_propagation true $bist_pins
     }
    }
   }
   icc_shell -
   icc2_shell {
    set nets [get_nets -boundary_type lower -of $bist_pins]
    switch $results(-dont_touch) {
     true {
      echo "Applying 'set_dont_touch' to constant BIST pins."
      set_dont_touch $nets
     }
     false {
      echo "Applying 'remove_attribute -name dont_touch' to constant BIST pins."
      redirect /dev/null {remove_attribute -quiet -objects $nets -name dont_touch}
     }
    }
   }
  }
 } elseif {$report} {
  # report
  _LB_eco_connect_signals {shift counter} $shift_counter_pins $shift_counter {report}
  _LB_eco_connect_signals {pattern counter} $pattern_counter_pins $pattern_counter {report}
  _LB_eco_connect_signals {PRPG seed} $PRPG_pins $PRPG_seed {report}
  _LB_eco_connect_signals {MISR signature} $MISR_pins $MISR_signature {report}
 } else {
  # set/write
  if {[info exists results(-write_vcs)]} {file delete $results(-write_vcs)}
  if {[info exists results(-write_1500)]} {file delete $results(-write_1500)}
  _LB_eco_connect_signals {shift counter} $shift_counter_pins $shift_counter [expr {$results(-force_shift_counter) ? {connect} : {check}}]
  _LB_eco_connect_signals {pattern counter} $pattern_counter_pins $pattern_counter {connect}
  _LB_eco_connect_signals {PRPG seed} $PRPG_pins $PRPG_seed {connect}
  _LB_eco_connect_signals {MISR signature} $MISR_pins $MISR_signature {connect}
  if {[info exists results(-write_1500)]} {
   if {[info exists mode_name]} {
    redirect -variable rpt {list_test_modes}
    if {[string first "Name: $mode_name\n" $rpt] == -1} {unset mode_name}
   }
   if {[info exists results(-test_mode)]} {
    set mode_name $results(-test_mode)
   }
   if {![info exists mode_name]} {
    error {Must specify -test_mode for top-level mode that tests 1500-inserted core.}
   }

   write_test -format stil -cdr_name CDR -output $results(-write_1500) \
    -seed $PRPG_seed \
    -signature $MISR_signature \
    -shift_counter $shift_counter \
    -pattern_counter $pattern_counter \
    -capture_cycle [lindex [list {01} {11}] $clock_cycles-1] \
    -test_mode $mode_name
  }
 }
}

define_proc_attributes set_logicbist_constants \
 -hide_body \
 -info "Set or report LogicBIST constant values for the current design" \
 -define_args \
 {
  {-file_name "Set to values read from this STIL serial pattern file" file_name string optional}
  {-force_shift_counter "Force constant-driven modification of shift-counter values" {} boolean optional}
  {-write_1500 "Write IEEE 1500 STIL testbench that sets CDR-driven values" file_name string optional}
  {-write_vcs "Write port-driven signal force commands to this VCS file" file_name string optional}
  {-test_mode "Specify top-level test mode that tests 1500-inserted core" test_mode string optional}
  {-dont_touch "Control whether constant values are preserved or optimized" {} one_of_string {optional value_help {values {true false}}}}
 } \
 -define_arg_groups {
  {together {-force_shift_counter -file_name}}
  {together {-write_1500 -file_name}}
  {together {-write_vcs -file_name}}
  {together {-test_mode -write_1500}}
  {exclusive {-write_1500 -force_shift_counter}}
  {exclusive {-write_vcs -write_1500}}
  {exclusive {-dont_touch -file_name}}
  {exclusive {-dont_touch -force_shift_counter}}
  {exclusive {-dont_touch -write_1500}}
  {exclusive {-dont_touch -write_vcs}}
  {exclusive {-dont_touch -test_mode}}
 }

