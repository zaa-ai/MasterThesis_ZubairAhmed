
set TECH [exec getPrjCfg.rb -p tech]

proc getLatestCEL {_library _view} {
    set index 0
    
    set filename [lindex [ls $_library/$_view -t1] $index]
    
    ## do not return "." or ".."
    if {[string length $filename] < 3} {
    	incr index
	set filename [lindex [ls $_library/$_view -t1] $index]
    }
    
    ## do not return "." or ".."
    if {[string length $filename] < 3} {
    	incr index
	set filename [lindex [ls $_library/$_view -t1] $index]
    }
	
    # remove CEL ":Version", latest is used
    set returnvalue [lindex [split $filename ":"] 0]
    return $returnvalue
}

#source user_tcl/icc_suppress_messages.tcl

source -echo $env(PROJECT_HOME)/scripts/misc/tcl/procs.tcl

source -echo user_tcl/common_setup.tcl
source -echo $env(PROJECT_HOME)/scripts/layout/tcl/icc/rm_setup/icc_setup.tcl

open_mw_lib $MW_DESIGN_LIBRARY
open_mw_cel [getLatestCEL $MW_DESIGN_LIBRARY CEL ]
