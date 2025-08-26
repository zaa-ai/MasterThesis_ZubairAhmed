source dump.tcl
if { [info exists ::env(GATE_LEVEL)] } {
	source tcheck.tcl
}
run
quit
