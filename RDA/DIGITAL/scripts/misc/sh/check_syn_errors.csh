#!/bin/tcsh -f
#--------- report errors

if ( "x$1" != "x" ) then
  set log_file=$1
else
  set log_file=`ls -1 -rt dc/dc.log* | tail -1`
endif

echo "----------------------------------------------"     >! rtl_syn.errors
echo ""                                                   >> rtl_syn.errors
ls -lh $log_file                                          >> rtl_syn.errors
echo ""                                                   >> rtl_syn.errors

#==========================================================================

echo "----------------------------------------------"     >> rtl_syn.errors
echo " structure warnings                           "     >> rtl_syn.errors
echo "----------------------------------------------"     >> rtl_syn.errors
echo ""                                                   >> rtl_syn.errors

grep VER- $log_file | \
  grep -v VER-209 | \
  grep -v VER-274 | \
  grep -v VER-318 | \
  grep -v VER-329 | \
  grep -v VER-533 | \
  grep -v VER-735 | \
  grep -v VER-936 >> rtl_syn.errors

echo ""                                                   >> rtl_syn.errors
echo "----------------------------------------------"     >> rtl_syn.errors
echo ""                                                   >> rtl_syn.errors

grep LINT- $log_file | \
  grep -v LINT-1  | \
  grep -v LINT-2  | \
  grep -v LINT-28 | \
  grep -v LINT-32 | \
  grep -v LINT-33 | \
  grep -v LINT-99 >> rtl_syn.errors

echo ""                                                   >> rtl_syn.errors
echo "----------------------------------------------"     >> rtl_syn.errors
echo ""                                                   >> rtl_syn.errors

grep ELAB- $log_file | \
  grep -v ELAB-311 >> rtl_syn.errors

echo ""                                                   >> rtl_syn.errors
echo "----------------------------------------------"     >> rtl_syn.errors
echo ""                                                   >> rtl_syn.errors

#==========================================================================

# removing unused register
grep "OPT-1207" $log_file                                 >> rtl_syn.errors
grep "OPT-1206" $log_file                                 >> rtl_syn.errors
echo ""                                                   >> rtl_syn.errors

#grep " : Unconnected input port " $log_file               >> rtl_syn.errors
#echo ""                                                   >> rtl_syn.errors
#
#grep " : Undriven bits of signal " $log_file              >> rtl_syn.errors
#echo ""                                                   >> rtl_syn.errors
#
#grep " : Undriven bits of port " $log_file                >> rtl_syn.errors
#echo ""                                                   >> rtl_syn.errors
#
#grep -A 1 "Warning : Input port connected to output instance port" $log_file \
#                                                          >> rtl_syn.errors
#echo ""                                                   >> rtl_syn.errors
#
#grep -A 1 "Warning : An interface-type port has no modport specified" $log_file \
#                                                          >> rtl_syn.errors
#echo ""                                                   >> rtl_syn.errors
# timing loops
mgrep $log_file \
  "TIM-209" \
  "Information:" "skip_end" \
                                                          >> rtl_syn.errors
echo "----------------------------------------------"     >> rtl_syn.errors
echo ""                                                   >> rtl_syn.errors
echo "FF's without reset/set in syn netlist"              >> rtl_syn.errors
grep "ERROR: no async pin found" $log_file                >> rtl_syn.errors
echo "----------------------------------------------"     >> rtl_syn.errors
echo ""                                                   >> rtl_syn.errors
#mgrep $log_file \
#  "The following sequential clock pins have no clock waveform driving" \
#  "-------------------------------------------------------------------------------" \
#                                                          >> rtl_syn.errors
#echo ""                                                   >> rtl_syn.errors
#mgrep $log_file \
#  "The following sequential data pins are driven by a clock signal" \
#  "-------------------------------------------------------------------------------" \
#                                                          >> rtl_syn.errors
#echo ""                                                   >> rtl_syn.errors
#mgrep $log_file \
#  "The following timing exceptions are not currently affecting timing" \
#  "-------------------------------------------------------------------------------" \
#                                                          >> rtl_syn.errors
#echo ""                                                   >> rtl_syn.errors

#==========================================================================

echo "----------------------------------------------"     >> rtl_syn.errors
echo " timing setup warnings                        "     >> rtl_syn.errors
echo "----------------------------------------------"     >> rtl_syn.errors
echo ""                                                   >> rtl_syn.errors

#Information: There are * clock pins driven by multiple clocks, and some of them are driven by up-to 2 clocks. (TIM-099)
#Warning: A non-unate path in clock network for clock * from pin * is detected. (TIM-052)
grep "TIM-" $log_file | grep -v "TIM-099" | grep -v "TIM-052" \
                                                          >> rtl_syn.errors

echo ""                                                   >> rtl_syn.errors

#==========================================================================

echo "----------------------------------------------"     >> rtl_syn.errors
echo " DFT rule violations                          "     >> rtl_syn.errors
echo "----------------------------------------------"     >> rtl_syn.errors
echo ""                                                   >> rtl_syn.errors
grep "D1-" $log_file                                      >> rtl_syn.errors
grep "D2-" $log_file                                      >> rtl_syn.errors
grep "D3-" $log_file                                      >> rtl_syn.errors
grep "D9-" $log_file                                      >> rtl_syn.errors
echo ""                                                   >> rtl_syn.errors

#echo "----------------------------------------------"     >> rtl_syn.errors
#echo " DFT mapping report                           "     >> rtl_syn.errors
#echo "----------------------------------------------"     >> rtl_syn.errors
#echo ""                                                   >> rtl_syn.errors
#mgrep $log_file \
#  "Scan flip-flops mapped for DFT" \
#  "Totals" \
#                                                          >> rtl_syn.errors
#echo ""                                                   >> rtl_syn.errors

echo "----------------------------------------------"     >> rtl_syn.errors
echo " DFT non scan object report                   "     >> rtl_syn.errors
echo "----------------------------------------------"     >> rtl_syn.errors
echo ""                                                   >> rtl_syn.errors
mgrep $log_file \
  "Flip Flops, which are not part of a scan chain:" \
  "Total:" \
                                                          >> rtl_syn.errors
echo ""                                                   >> rtl_syn.errors

#grep -A 1 "Warning : Scan mapped flop fails DFT rule check" $log_file \
#                                                          >> rtl_syn.errors
#echo ""                                                   >> rtl_syn.errors

#==========================================================================

echo "----------------------------------------------"     >> rtl_syn.errors
echo " error and register summary for synthesis:"         >> rtl_syn.errors
echo "----------------------------------------------"     >> rtl_syn.errors
echo ""                                                   >> rtl_syn.errors
grep "^Error" $log_file                                   >> rtl_syn.errors
grep "SPG-013" $log_file                                  >> rtl_syn.errors
echo ""                                                   >> rtl_syn.errors
mgrep $log_file \
  "report.tcl" \
  "bugs bunny" | grep "slack"                             >> rtl_syn.errors
#grep "(Timing slack|report.tcl)" $log_file                             >> rtl_syn.errors
echo ""                                                   >> rtl_syn.errors

#==========================================================================

echo "----------------------------------------------"     >> rtl_syn.errors

cat rtl_syn.errors
