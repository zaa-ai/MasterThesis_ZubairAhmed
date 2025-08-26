#################################################################################
# Write out scripts for TMAX to generate "hübsche" Pattern for the TINGs
#
#
#################################################################################

########################################################
set SCAN_CLK    [exec getPrjCfg.rb config/test/scan_clk]
set SCAN_SCK    [exec getPrjCfg.rb config/test/scan_sck]
set SCAN_ENABLE [exec getPrjCfg.rb config/test/scan_enable]
set TEST_MODE   [exec getPrjCfg.rb config/test/test_mode]
set SCAN_RES    [exec getPrjCfg.rb config/test/scan_res]
set SCAN_DIN1   [exec getPrjCfg.rb config/test/scan_din1] 
set SCAN_DOUT1  [exec getPrjCfg.rb config/test/scan_dout1]
set SCAN_DIN2   [exec getPrjCfg.rb config/test/scan_din2] 
set SCAN_DOUT2  [exec getPrjCfg.rb config/test/scan_dout2]
set SCAN_DIN3   [exec getPrjCfg.rb config/test/scan_din3] 
set SCAN_DOUT3  [exec getPrjCfg.rb config/test/scan_dout3]
set PORB        [exec getPrjCfg.rb config/test/porb]
set TDI         [exec getPrjCfg.rb config/test/tdi]; # should not be removed from protocoll file


set ScanPorts [list $SCAN_CLK \
	$SCAN_SCK \
	$SCAN_ENABLE \
	$TEST_MODE \
	$SCAN_RES \
	$SCAN_DIN1 \
	$SCAN_DIN2 \
	$SCAN_DIN3 \
	$SCAN_DOUT1 \
	$SCAN_DOUT2 \
	$SCAN_DOUT3 \
	$PORB \
        $TDI  ]
########################################################
set i 0
set Pattern ""
foreach PORT $ScanPorts {
    set pattern_part ""
    regsub -all {\[} $PORT "\\\[" pattern_part ;# to replace bus vectors [x] in regexp to \[x\]
    regsub -all {\]} $pattern_part "\\\]" pattern_part
    if ($i!=0) {
	append Pattern "|";# to append more than one signal in regexp
    }
    append Pattern "^${pattern_part}$"
    set i [expr $i+1]
}
puts "Pattern is ${Pattern}" ;# logging in shell

set file "${RESULTS_DIR}/nonDFT_out_signals_file.txt" ;# configuration file of spfgen.pl to remove ports from spf-file
file mkdir [file dirname $file]
set f [open $file w]
foreach_in_collection PORT [all_outputs] { ;# for all outputs except scan ports
    if [regexp -nocase ${Pattern} [get_object_name $PORT]] {
	puts "Scan port: [get_object_name ${PORT}]" ;# logging in shell
    } else {
	puts $f "[get_object_name ${PORT}]" ;# spfgen --> remove port from spf-file
	puts "Put [get_object_name $PORT] to nonDFT_out_signals_file.txt" ;# logging in shell
    }
}
close $f

set file "${RESULTS_DIR}/nonDFT_in_signals_file.txt" ;# configuration file of spfgen.pl to remove ports from spf-file
file mkdir [file dirname $file]
set f [open $file w]

foreach_in_collection PORT [all_inputs] { ;# for all inputs except scan ports
    if [regexp -nocase ${Pattern} [get_object_name $PORT]] {
	puts "Scan port: [get_object_name ${PORT}]" ;# logging in shell
    } else {
	    puts $f "[get_object_name ${PORT}]" ;# spfgen --> remove port
	    puts "remove port: [get_object_name $PORT]" ;# logging in shell
#	    if [regexp -nocase "^vdd$|^vcc$|^vss$|^gnd$|^vsub$" [get_object_name ${PORT}]] {;#damit vdd,gnd und vsub nicht mit genommen werden
#		    } else {
#	    if [regexp -nocase "porn|por_n|rst_n|rstn|porb|por_b" [get_object_name ${PORT}]] {
#	    } else {
#		if [regexp -nocase "por|rst|reset|vsuv_i" [get_object_name ${PORT}]] {
#		    } else {
#	       }
#		}
#	}
    }
}
close $f ;#close files

# delete file if it exists to overwrite
#if [file exist "${RESULTS_DIR}/pattern/digtop.mapped.comp.spfgen.config"] {
#    file delete "${RESULTS_DIR}/pattern/digtop.mapped.comp.spfgen.config"
#}
#if [file exist "${RESULTS_DIR}/pattern/digtop.mapped.spfgen.config"] {
#    file delete "${RESULTS_DIR}/pattern/digtop.mapped.spfgen.config"
#}
#file mkdir "${RESULTS_DIR}/pattern"
#file copy $file "${RESULTS_DIR}/pattern/digtop.mapped.comp.spfgen.config"
#file copy $file "${RESULTS_DIR}/pattern/digtop.mapped.spfgen.config"
#
#if [file exist "${RESULTS_DIR}/pattern/digtop.mapped.tmax.tcl"] {
#    file delete "${RESULTS_DIR}/pattern/digtop.mapped.tmax.tcl"
#}
#file copy $file_tcl "${RESULTS_DIR}/pattern/digtop.mapped.tmax.tcl"
#
#report_area -hierarchy 
