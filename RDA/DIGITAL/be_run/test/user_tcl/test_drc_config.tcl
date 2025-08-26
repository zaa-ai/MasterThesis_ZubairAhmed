puts "RM-Info: Running script [info script]\n"

set NONDFT_IN_SIGNAL_FILE   "../syn/results/nondft_in.signals"
set NONDFT_OUT_SIGNAL_FILE  "../syn/results/nondft_out.signals"

################################################################
##                  Configure PATTERNEXEC                     ##
################################################################

if {$env(OCC) eq "1"} {
    if {$env(COMP) eq "1"} {
	set PATTERNEXEC "ScanCompression_mode"
    } else {
	set PATTERNEXEC "Internal_scan"
    }
} else {
    if {$env(COMP) eq "1"} {
	set PATTERNEXEC "ScanCompression_mode_occ_bypass"
    } else {
	set PATTERNEXEC "Internal_scan_occ_bypass"
    }
}


################################################################
##              Remove non used signals from SPF              ##
################################################################

## ELMOS: Generate List of signals not used for DFT
##
set NONDFT_SIGNALS ""
foreach NONDFT_SIGNAL_FILE "$NONDFT_IN_SIGNAL_FILE $NONDFT_OUT_SIGNAL_FILE" {
   if [file exists $NONDFT_SIGNAL_FILE] {
       set fd [open $NONDFT_SIGNAL_FILE r]
       append NONDFT_SIGNALS [read $fd]
       close $fd
   }
}

## ELMOS: Remove unnecessary Signals from ${PROTOCOL_FILE} before running DRC
##
if {$NONDFT_SIGNALS != ""} {
    set fd [open ${PROTOCOL_FILE}.config w ]
    if {$PATTERNEXEC != ""} {
	puts $fd  "INPUT_SPF ${PROTOCOL_FILE} -patternexec ${PATTERNEXEC}"
    } else {
	puts $fd  "INPUT_SPF ${PROTOCOL_FILE}"
    }
    puts $fd  "OUTPUT_SPF ${PROTOCOL_FILE}_clean"
    foreach signal $NONDFT_SIGNALS {
       if  {$signal != ""} {
          puts $fd "REMOVE_PORT $signal"
       }
    }
    close $fd
#ELMOS: switched from SYNOPSYS to TMAXSHELL
    exec [getenv {TMAX_SHELL}]/auxx/syn/tmax/spfgen.pl ${PROTOCOL_FILE}.config
    append PROTOCOL_FILE "_clean"
}

################################################################
##              Specify Timing for SCAN Clocks                ##
################################################################
drc -force
read_drc ${PROTOCOL_FILE}

update_wft   -wft { _default_WFT_ _allclock_launch_capture_WFT_ _multiclock_capture_WFT_ _allclock_launch_WFT_ _allclock_capture_WFT_ } -period 100000 -strobe 23000 -unit ps
update_clock -wft { _default_WFT_ _allclock_launch_capture_WFT_ _multiclock_capture_WFT_ _allclock_launch_WFT_ _allclock_capture_WFT_ } -clock i_clk     -pulse { 25 75 } -unit ns
update_clock -wft { _default_WFT_ _allclock_launch_capture_WFT_ _multiclock_capture_WFT_ _allclock_launch_WFT_ _allclock_capture_WFT_ } -clock i_sclk    -pulse { 25 75 } -unit ns
update_clock -wft { _default_WFT_ _allclock_launch_capture_WFT_ _multiclock_capture_WFT_ _allclock_launch_WFT_ _allclock_capture_WFT_ } -clock i_resq_n  -pulse { 25 75 } -unit ns
update_clock -wft { _default_WFT_ _allclock_launch_capture_WFT_ _multiclock_capture_WFT_ _allclock_launch_WFT_ _allclock_capture_WFT_ } -clock i_clk_24m -pulse { 25 75 } -unit ns

append PROTOCOL_FILE "_updated"
write_drc ${PROTOCOL_FILE} -replace

set NONDFT_IN_SIGNAL_FILE   ""
set NONDFT_OUT_SIGNAL_FILE  ""
set PATTERNEXEC ""
