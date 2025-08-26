# (c) 2017 Synopsys, Inc.  All rights reserved.
#
# This script is proprietary and confidential information of
# Synopsys, Inc. and may be used and disclosed only as authorized
# per your agreement with Synopsys, Inc. controlling such use and
# disclosure.


# find_seed.tcl
#  rerun LogicBIST ATPG repeatedly to find a seed with optimal coverage
#
# v1.0  06/25/2015 chrispy
#  initial release
# v1.1  08/01/2015 chrispy
#  preserve initial fault list
# v1.2  10/12/2015 chrispy
#  fix divide-by-zero exception in seed 20 when stddev is zero
# v1.3  03/22/2016 chrispy
#  show binary seed values
#  get rid of external pattern cache, rerun best seed at end
#  -sigma and -seed_count are no longer mutually exclusive
# v1.4  06/13/2016 chrispy
#  show ATPG effectiveness
# v2.0  05/18/2017 chrispy
#  implement significant speedup
#  add -num_seeds option
#  rename -seed_count to -search_limit
#  implement -time_limit
#  remove -sigma
# v2.1  02/14/2018 chrispy
#  fix a bug in STIL file output for multiple seeds
# v2.2  11/01/2018 chrispy
#  reduce correlation between adjacent seed value trials
# 16/09/2022 ELMOS(makoe): added a check for exit code 1 of regexp statement


proc _fs_dtob {seed length} {
 set seed_binary {}
 for {set i 1} {$i <= $length} {incr i} {
  set seed_binary "[expr int($seed)%2]${seed_binary}"
  set seed [expr int($seed/2)]
 }
 return $seed_binary
}
define_proc_attributes _fs_dtob -hide_body -hidden -dont_abbrev

proc _fs_swizzle {word} {
 if {![info exists ::_fs_positions]} {
  set wordwidth [string length $word]
  set cntwidth [expr {int(ceil(log($wordwidth)/log(2)))}]
  for {set i 0} {$i <= [expr {(2**$cntwidth)-1}]} {incr i} {
   if {[set revpos [expr "0b[string reverse [_fs_dtob $i $cntwidth]]"]] < $wordwidth} {
    lappend positions $revpos
   }
  }
  set ::_fs_positions [concat [lrange $positions 1 end] [lindex $positions 0]]
 }
 foreach pos $::_fs_positions {append newword [string index $word $pos]}
 return $newword
}
define_proc_attributes _fs_swizzle -hide_body -hidden -dont_abbrev

proc _fs_gray {word} {
 set inv 0
 foreach bit [split $word {}] {
  append newword [set inv [expr {$inv ^ $bit}]]
 }
 return $newword
}
define_proc_attributes _fs_gray -hide_body -hidden -dont_abbrev

proc _fs_shift {offset word} {
 set l [string length $word]
 return [string range [string repeat $word 3] $l+$offset [expr {$l*2+$offset-1}]]
}
define_proc_attributes _fs_shift -hide_body -hidden -dont_abbrev

# code adapted from "math::statistics 0.6"
proc _fs_stats { type values } {
    variable TOOFEWDATA

    set min    {}
    set max    {}
    set mean   {}
    set stdev  {}
    set var    {}

    set sum    0.0
    set sumsq  0.0
    set number 0

    foreach value $values {
	if { $value == {} } {
	    continue
	}
	set value [expr {double($value)}]

	incr number
	set  sum    [expr {$sum+$value}]
	set  sumsq  [expr {$sumsq+$value*$value}]

	if { $min == {} || $value < $min } {
	    set min $value
	}
	if { $max == {} || $value > $max } {
	    set max $value
	}
    }

    if { $number > 0 } {
	set mean [expr {$sum/$number}]
    } else {
	return -code error -errorcode DATA -errorinfo $TOOFEWDATA $TOOFEWDATA
    }

    if { $number > 1 } {
	set var    [expr {($sumsq-$mean*$sum)/double($number-1)}]
        #
        # Take care of a rare situation: uniform data might
        # cause a tiny negative difference
        #
        if { $var < 0.0 } {
           set var 0.0
        }
	set stdev  [expr {sqrt($var)}]
    }
	set pvar [expr {($sumsq-$mean*$sum)/double($number)}]
        #
        # Take care of a rare situation: uniform data might
        # cause a tiny negative difference
        #
        if { $pvar < 0.0 } {
           set pvar 0.0
        }
	set pstdev  [expr {sqrt($pvar)}]

    set all [list $mean $min $max $number $stdev $var $pstdev $pvar]

    #
    # Return the appropriate value
    #
    if { [lsearch {all mean min max number stdev var pstdev pvar} $type] >= 0 } {
	# FRINK: nocheck
	return [set $type]
    } else {
	return -code error \
		-errorcode ARG -errorinfo [list unknown type of statistic -- $type] \
		[list unknown type of statistic -- $type]
    }
}
define_proc_attributes _fs_stats -hide_body -hidden -dont_abbrev

proc _fs_total_faults {} {
 redirect -variable rpt {report_faults -summary}
 regexp -line {^ total faults +(\d+)$} $rpt dummy total_faults
 return $total_faults
}
define_proc_attributes _fs_total_faults -hide_body -hidden -dont_abbrev

proc _fs_run_atpg {seed faults command} {
 add_lbist_seed -format binary_normal "0:$seed"
 if {$faults ne {}} {
  redirect /dev/null {
   set_patterns -delete
   read_faults $faults -force_retain_code
  }
 }
 redirect -variable rpt {eval $command}
 if {![regexp -line {^ test coverage +(\S+)%} $rpt dummy coverage] || ![regexp -line {^ ATPG effectiveness +(\S+)%} $rpt dummy effectiveness] || ![regexp -line {^ Not detected\s+ND\s+(\d+)} $rpt dummy ND_count]} {
  file delete -force {*}[glob "/tmp/tmax_find_seed_[pid]_*.flt.bin"]
  error {run_atpg failed}
  return 0
 }
 return [list $coverage $effectiveness $ND_count]
}
define_proc_attributes _fs_run_atpg -hide_body -hidden -dont_abbrev




proc find_seed {args} {
 set results(-first_seed) 1
 set results(-num_seeds) 1
 parse_proc_arguments -args $args results

 unset -nocomplain ::_fs_positions   ;# reset any cached swizzling information

 # get seed length
 catch {redirect -variable rpt {add_lbist_seeds -format binary_normal 0:1}}

 #ELMOS: added a check for exit code 1
 #regexp {careprpg cells (\d+)} $rpt dummy LBIST_SEED_LENGTH
 set status [catch {regexp {careprpg cells (\d+)} $rpt dummy LBIST_SEED_LENGTH}]
 if {$status == 0} {
    puts $rpt
 }

 # process arguments
 if {[string first {-jtag_lbist} $results(command)] == -1} {
  error "Cannot evaluate seed values; the -jtag_lbist option is not specified on the command line."
 }
 if {[info exists results(-search_limit)]} {
  if {$results(-search_limit) < 2} {
   error "Seed count '$results(-search_limit)' must be an integer greater than 1."
  }
  set search_limit 1
 } else {
  set search_limit 0
 }
 if {[info exists results(-time_limit)]} {
  set seconds_final_target [expr {[clock seconds]+int($results(-time_limit)*60.0)}]
  set time_limit 1
 } else {
  set time_limit 0
 }
 if {!$search_limit && !$time_limit} {
  error "At least one of the following options must be specified: -search_limit, -time_limit"
 }

 # enable ATPG effectiveness reporting
 set_patterns -internal
 set_faults -atpg_effectiveness

 # add all faults if they're missing
 redirect -variable rpt {report_faults -summary}
 if {[regexp -line {^ total faults +0$} $rpt]} {
  add_faults -all
  echo ""
 }
 set total_faults_initial [_fs_total_faults]

 # make sure we evaulate every seed with the current fault list
 set initial_fault_file /tmp/tmax_find_seed_[pid]_initial.flt.bin
 set almost_initial_fault_file /tmp/tmax_find_seed_[pid]_almost.flt.bin
 set current_fault_file /tmp/tmax_find_seed_[pid]_current.flt.bin
 set best_fault_file /tmp/tmax_find_seed_[pid]_best.flt.bin
 set drop_fault_file /tmp/tmax_find_seed_[pid]_drop.flt.bin
 redirect /dev/null { write_faults $initial_fault_file -all -replace -compress binary }


################################
# remove easy faults for faster searching
echo "Removing easy faults..."

# get pattern count so we can work with a proportionally reduced pattern count
if {![regexp {(.*-jtag_lbist\s+[\{"]\s*)(\d+)\s+(\d+)(\s+\d+[\s\}"].*)} $results(command) dummy pre seedcount patcount post]} {
 file delete -force {*}[glob "/tmp/tmax_find_seed_[pid]_*.flt.bin"]
 error {Could not obtain pattern count from command.}
}
if {$seedcount != 1} {
 echo {Warning: Seed count (first argument of -jtag_lbist) should be 1; use -num_seeds to find multiple seeds.}
}

# remove easy faults, starting with super-easy and working downward
set total 30
set start 3
set ratio 0.90
set easy_command "${pre}${seedcount} [expr {1+int(0.5+1.0*($patcount-1)/8)}]${post}"
redirect /dev/null { file copy -force $initial_fault_file $current_fault_file }

for {set seed 1} {$seed <= $total} {incr seed} {
 # measure time of first full run with no faults removed
 if {$seed==($start+1)} {set atpg_us [clock microseconds]}
 if {$seed==($start+2)} {set atpg_us [expr {[clock microseconds]-$atpg_us}]}

 lassign [_fs_run_atpg [_fs_gray [_fs_swizzle [_fs_dtob $seed $LBIST_SEED_LENGTH]]] {} $easy_command] this_coverage this_effectiveness this_ND_count  ;# only a bit of scrambling for easy fault removal
 redirect /dev/null {
  write_faults $drop_fault_file -class DT -replace
  set_patterns -delete
  read_faults $current_fault_file -force_retain_code
 }

 set dt_file [open $drop_fault_file]
 while {[gets $dt_file line] != -1} { incr dt_count($line) }
 close $dt_file

 set drop_total 0
 if {$seed >= $start} {
  set limit [expr {int($seed*(1-(1.0*($seed-$start)/($total-$start)*$ratio)))}]
  redirect $drop_fault_file {
   foreach key [array names dt_count] {
    if {$dt_count($key) >= $limit} {
     echo $key
     unset dt_count($key)
     incr drop_total
    }      
   }
  }
 }
 if {$drop_total > 0} {
  redirect /dev/null {
   read_faults $drop_fault_file -delete
   write_faults $current_fault_file -all -replace -compress binary
   set this_total_faults [_fs_total_faults]
  }
  echo [format {  %d faults dropped, %d (%.2f%%) remain} $drop_total $this_total_faults [expr {100.0*$this_total_faults/$total_faults_initial}]]
 }
 if {$seed == $start} {
  redirect /dev/null {write_faults $almost_initial_fault_file -all -replace -compress binary}
 }
}
file delete -force $drop_fault_file
################################



 # search seeds to find best outcome
 set seed [expr {$results(-first_seed)}]
 set seed_count_width [expr {$search_limit ? [string length $results(-search_limit)] : 6}]
 for {set iter 0} {$iter <= $results(-num_seeds)} {incr iter} {
  if {$iter == 0} {
   echo "\n\nStarting search for best seed[expr {$results(-num_seeds) > 1 ? " #1" : {}}] with reduced fault list..."
  } elseif {$iter == 1} {
   echo "\n  Refining results using more complete fault list..."
  } else {
   echo "\n\nFinding best seed #${iter} using nondetected faults from previous iteration..."
  }
  echo "\n   Trial  [format "%-${LBIST_SEED_LENGTH}s" {Seed}]           Coverage      Effectiveness    Best so far?"
  echo "  [string repeat {=} 6]  [string repeat {=} ${LBIST_SEED_LENGTH}]    [string repeat {=} 15]    [string repeat {=} 15]    [string repeat {=} 12]"
  if {$time_limit && $iter != 1} {
   if {$iter == 0} {
    set seconds_this_target [expr {int([clock seconds]+($seconds_final_target-[clock seconds])/($results(-num_seeds))-(8.0*$atpg_us/1e6))}]
   } else {
    set seconds_this_target [expr {int([clock seconds]+($seconds_final_target-[clock seconds])/($results(-num_seeds)-($iter-1)))}]
   }
  }
  redirect /dev/null {
   # remove detected faults (original or from previous iteration)
   remove_fault -class dt
   write_faults $current_fault_file -all -replace -compress binary
  }
  set total_faults_current [_fs_total_faults]

  set best_ND_count inf
  set coverages {}
  set effectivenesses {}
  if {$iter == 0} {set effectiveness_for_seed {}}
  set i 1
  while {1} {
   if {$iter != 1} {
    set seed_binary [_fs_gray [_fs_swizzle [_fs_gray [_fs_swizzle [_fs_dtob $seed $LBIST_SEED_LENGTH]]]]]  ;# change the seed scrambling here
   } else {
    if {$i > 20 || $i > [llength $effectiveness_for_seed]} {break}
    set seed_binary [lindex [lindex $effectiveness_for_seed $i-1] 0]
   }
   lassign [_fs_run_atpg $seed_binary $current_fault_file $results(command)] this_coverage this_effectiveness this_ND_count

   set this_coverage [expr {(($this_coverage*$total_faults_current)+(100.00*($total_faults_initial-$total_faults_current)))/$total_faults_initial}]
   set this_effectiveness [expr {(($this_effectiveness*$total_faults_current)+(100.00*($total_faults_initial-$total_faults_current)))/$total_faults_initial}]
   lappend coverages $this_coverage
   lappend effectivenesses $this_effectiveness
   if {$iter == 0} {lappend effectiveness_for_seed [list $seed_binary $this_effectiveness]}

   if {$i >= 20} {
    set cov_mean [_fs_stats mean $coverages]
    set cov_pstdev [_fs_stats pstdev $coverages]
    set cov_stdev [expr {$cov_pstdev > 0 ? (($this_coverage-$cov_mean)/$cov_pstdev) : 0.0}]
    set eff_mean [_fs_stats mean $effectivenesses]
    set eff_pstdev [_fs_stats pstdev $effectivenesses]
    set eff_stdev [expr {$eff_pstdev > 0 ? (($this_effectiveness-$eff_mean)/$eff_pstdev) : 0.0}]
    echo -n [format "  %6d  %-${LBIST_SEED_LENGTH}s    (%+1.2fs)  %3.2f    (%+1.2fs)  %3.2f" $i $seed_binary $cov_stdev $this_coverage $eff_stdev $this_effectiveness]
   } else {
    echo -n [format "  %6d  %-${LBIST_SEED_LENGTH}s              %3.2f              %3.2f" $i $seed_binary $this_coverage $this_effectiveness]
   }
   if {$this_ND_count < $best_ND_count} {
    echo -n {    *}
    set best_effectiveness $this_effectiveness
    set best_ND_count $this_ND_count
    set best_seed_binary($iter) $seed_binary
    if {$iter < $results(-num_seeds)} {
     redirect /dev/null { write_faults $best_fault_file -all -replace -compress binary }
    }
   }
   echo ""
#echo "DATA: $this_coverage $this_effectiveness"
   incr seed

   if {$iter == 1} {
    if {([_fs_stats mean [lrange $effectivenesses end-7 end]]+2.5*[_fs_stats pstdev [lrange $effectivenesses end-7 end]]) < $best_effectiveness} {break}
   } else { 
    if {$search_limit && $i == $results(-search_limit)} {break}
    if {$time_limit && [clock seconds] >= $seconds_this_target} {break}
   }
   incr i
  }

  if {$iter < $results(-num_seeds)} {
   if {$iter == 0} {
    set effectiveness_for_seed [lsort -index 1 -real -decreasing $effectiveness_for_seed]
    redirect /dev/null {
     set_patterns -delete
     file rename -force $almost_initial_fault_file $current_fault_file
     read_faults $current_fault_file -force_retain_code
    }
   } elseif {$iter == 1} {
    echo "  Refinement complete."
    redirect /dev/null {
     set_patterns -delete
     read_faults $initial_fault_file -force_retain_code
     add_lbist_seed -format binary_normal "0:$best_seed_binary(1)"
     eval $results(command)
     set_patterns -delete
    }
   } else {
    redirect /dev/null {
     set_patterns -delete
     read_faults $best_fault_file -force_retain_code
    }
   }
  }

  if {$iter != 1} {
   echo "\n  Search statistics (estimated):"
   echo "  ------------------------------"
   echo [format "        Min test coverage: %.2f%%        Min ATPG effectiveness: %.2f%%" [::tcl::mathfunc::min {*}$coverages] [::tcl::mathfunc::min {*}$effectivenesses]]
   echo [format "    Average test coverage: %.2f%%    Average ATPG effectiveness: %.2f%%" [expr {[::tcl::mathop::+ {*}$coverages]/[llength $coverages]}] [expr {[::tcl::mathop::+ {*}$effectivenesses]/[llength $effectivenesses]}]]
   echo [format "        Max test coverage: %.2f%%        Max ATPG effectiveness: %.2f%%" [::tcl::mathfunc::max {*}$coverages] [::tcl::mathfunc::max {*}$effectivenesses]]
  }
 }
 unset -nocomplain ::_fs_positions   ;# reset any cached swizzling information

 echo "\n\nFinal best-seed coverage[expr {$results(-num_seeds) > 1 ? {s} : {}}]:\n"

 redirect /dev/null {
  remove_faults -all
  read_faults $initial_fault_file -force_retain_code
 }
 file delete -force {*}[glob "/tmp/tmax_find_seed_[pid]_*.flt.bin"]

 redirect -tee seeds_tmax.tcl {
  echo [string repeat {#} 48]
  for {set iter 1} {$iter <= $results(-num_seeds)} {incr iter} {
   echo {set_patterns -delete  ;# so output STIL files aren't cumulative}
   set_patterns -delete
   echo "add_lbist_seed -format binary_normal {0:$best_seed_binary($iter)}  ;\# seed[expr {$results(-num_seeds) > 1 ? " #${iter}" : {}}]\n"
   add_lbist_seed -format binary_normal "0:$best_seed_binary($iter)"

   echo "$results(command)"
   redirect -variable rpt {eval $results(command)}
   regsub {.*\n(?= +Uncollapsed)} $rpt {} rpt
   regsub {\n$} $rpt {} rpt
   regsub -all -line {^} $rpt {#} rpt
   echo "$rpt\n"

   set outfile "seed[expr {$results(-num_seeds) > 1 ? "$iter" : {}}].stil"
   echo "write_patterns $outfile -format stil -serial -replace"
   redirect -variable rpt {write_patterns $outfile -format stil -serial -replace}
   regsub {\n$} $rpt {} rpt
   regsub -all -line {^} $rpt {#} rpt
   echo "$rpt"

   if {$iter < $results(-num_seeds)} {echo ""}
  }
  echo [string repeat {#} 48]
 }

 echo "\nOutput files:"
 echo "  seeds_tmax.tcl"
 for {set iter 1} {$iter <= $results(-num_seeds)} {incr iter} {echo "  seed[expr {$results(-num_seeds) > 1 ? "$iter" : {}}].stil"}
 echo ""
}

define_proc_attributes find_seed \
 -info "Find a LogicBIST seed value with optimal coverage" \
 -define_args \
 {
  {-num_seeds "Number of best seed values to find" count int optional}
  {-time_limit "Number of minutes allowed (across all best seeds)" mins int optional}
  {-search_limit "Number of candidate seeds to evaluate (per each best seed)" count int optional}
  {-first_seed "Seed number to start search at" value int optional}
  {command "run_atpg command line to run" command string required}
 }

