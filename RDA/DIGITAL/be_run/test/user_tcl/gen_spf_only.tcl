puts "RM-Info: Running script [info script]\n"

#source -echo user_tcl/test_setup.tcl

# The default STIL protocol file is the DC-RM output.
# # If you are not using the DC-RM, change the variable in tmax_setup.tcl.
#
# ## ELMOS: Generate List of signals not used for DFT
 
set NONDFT_IN_SIGNAL_FILE   "./stil/nonDFT_in_signals_file.txt"
set NONDFT_OUT_SIGNAL_FILE  "./stil/nonDFT_out_signals_file.txt"
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
set PROTOCOL_FILES [list ./stil/digtop.mapped.iddq.spf ./stil/digtop.mapped.scan.spf ./stil/digtop.mapped.scancompress.spf]

if {$NONDFT_SIGNALS != ""} {
	foreach PROTOCOL_FILE "${PROTOCOL_FILES}" {
		set fd [open ${PROTOCOL_FILE}.config w ]
			puts $fd  "INPUT_SPF ${PROTOCOL_FILE}"
			puts $fd  "OUTPUT_SPF ${PROTOCOL_FILE}_o"
			foreach signal $NONDFT_SIGNALS {
				if  {$signal != ""} {
					puts $fd "REMOVE_PORT $signal"
				}
			}
		close $fd
	#ELMOS: switched from SYNOPSYS to TMAXSHELL
	exec [getenv {TMAX_SHELL}]/auxx/syn/tmax/spfgen.pl ${PROTOCOL_FILE}.config
	# Change the Pinnames to the Pinnames of the ATE
	exec script/patch_spf.rb ${PROTOCOL_FILE}_o > ${PROTOCOL_FILE}_ATE_pins
	}
} else {
	puts "There are no signals to remove"	
}

exit
