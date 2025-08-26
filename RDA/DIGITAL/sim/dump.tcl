if { [info exists ::env(TESTCASE)] } {
  dump -file $env(TESTCASE).fsdb -type FSDB
}
set dumpType FSDB
dump -deltaCycle on
dump -msv on
if {$dumpType eq "FSDB"} {
  dump -add top_tb -fsdb_opt +all
} else {
  dump -add top_tb.* -aggregates
}
