#!/bin/csh
# Add at top module to int  output.v netlist Powerports for gate level simulation

set orig_file  = "$PROJECT_HOME/be_run/layout/results/digtop.output.v"
set patch_file = "$PROJECT_HOME/be_run/layout/results/digtop.output.pg.v"
cp -vf ${orig_file} ${patch_file}
perl -pi.bak -e 'undef $/; s/module digtop\s*\(([^;]*)\);/module digtop \(\1, VDD , VSS , VCC , VDD_NBL , PSUB \);\ninput VDD, VSS, VCC, VDD_NBL, PSUB ;/gs' ${patch_file}
rm -f ${patch_file}.bak

