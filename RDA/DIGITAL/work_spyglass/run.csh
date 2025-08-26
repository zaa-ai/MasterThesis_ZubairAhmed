#!/bin/csh
source cleanup.csh

spyglass -project digtop.prj -designread -batch

if ($#argv > 1) then
	echo "run with arguments"
	set arg = $argv[1]

	# LINT analysis batch: 
	spyglass -project digtop.prj -goals "lint/lint_rtl" $arg
	# CDC setup
	#spyglass -project digtop.prj -goals "cdc/cdc_setup,cdc/cdc_setup_check,cdc/clock_reset_integrity,cdc/cdc_verify_struct,cdc/cdc_verify" $arg
	# RDC setup
	#spyglass -project digtop.prj -goals "rdc/rdc_verify_struct" $arg
	
else
	echo "run without arguments"
	spyglass -project digtop.prj -goals "cdc/cdc_setup,cdc/cdc_setup_check,cdc/clock_reset_integrity,cdc/cdc_verify_struct,cdc/cdc_verify"
endif

unset arg
