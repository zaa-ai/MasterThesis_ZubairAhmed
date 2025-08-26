#!/usr/bin/perl

############################################################################################
# (C) COPYRIGHT 2020 ELMOS Semiconductor SE
# ALL RIGTHS RESERVED
#
# Date:   2021-06-15
# Author: MAKOE
#
# Info: This Script is intended to parse the tetramax output logfile and to extract
#       the coverage values for the fault simulation and ATPG run per Fault Model.
#
#       Printed Output format:
#       ------------------------------------------------------------------------------------------
#       Fault Model  Patterns  Patterns  Test Cycles  Test Cycles  Coverage  Covergae  SlackBased      
#                              (Total)                (Total)       (Test)   (Fault)                              
#       ------------------------------------------------------------------------------------------
#
#
#       Additional generated files (if enabled with -p):
#       --------------------------------------------------------------------------------
#       <reports dir>/coverages/<fault model>
#                     |         |/<fault_sim>.dat   (containing pat-count and coverage)
#                     |         |/<atpg_run>.dat    (containing pat-count and coverage)
#                     |         |/<fault model>.gpt (gnuplot script to generate png chart)
#                     |         |/<fault model>.png (png chart for coverage vs. pat-count)
#                     |
#                     |/index.html                  (HTML Page to show all results)
# 
############################################################################################


############################################################################################
# analyze script arguments
############################################################################################
use Getopt::Std;
my $opt_string = 'qhvtpl:r:';
getopts( "$opt_string", \%opt ) or usage();
usage() if $opt{h};

# do not open firefox
#
my $quiet = "$opt{q}";

# print debug output {-v}
#
my $verbose = "$opt{v}";

# calculate total coverage {-t}   <---- hidden feature
#   All dyn and stat faults accumulated, just for interrest.
#   Maybe more usefull if splitted between dyn and stat....
#   -> to be continued
my $total_cov = "$opt{t}";

# define report directory {-r <dir>}
#
my $folder = $opt{r};
if ($folder eq "") {$folder = "reports/coverage"}

# define logfile to be parsed {-l <file>}
#
my $logfile = "$opt{l}";


# generate coverage plot {-p}
#
my $gnu_plot = "$opt{p}";


############################################################################################
# common variables
############################################################################################

my $design_name           = "";

my $drc_active            = 0;

my $atpg_active           = 0;
my $atpg_run              = 0;
my $fault_sim             = 0;

my $fault_model           = "";

my $atpg_patterns_total   = 0;
my $atpg_cycles_total     = 0;
my %atpg_faults_total     = ();
my $test_cov_column       = 0;
my $test_cnt_column       = 0;
		          
%SCAN_ARCH   = ();
%FAULT_MODEL = ();
%INCR_FAULTS = ();


############################################################################################
# clear reports folder
############################################################################################

############################################################################################
# parse logfile
############################################################################################

open(INPUT, $logfile) or usage();

while (<INPUT>) {
    chomp ($_);

    $line = $_;
    $line =~ s/\// /g;
    $line =~ s/^\s+//;

    @column = split(/\s+/, $line);

    ####################################################################################
    # Detect Design Name
    ####################################################################################

    if (/^\s* Begin build model for topcut = (.*) .*/) {
       $design_name = $1;
       print ("LOGFILE: $_\n") if $verbose >= 1;
    }

    ####################################################################################
    # Detect DRC
    ####################################################################################

    # DRC Begin
    #
    elsif (/^\sBegin reading test protocol file .*\/(.*)\.\.\.$/) {
	$drc_active = 1;

	print ("########################################################################\n") if $verbose >= 1;
	print ("LOGFILE: $_\n")                                                              if $verbose >= 1;
	print ("########################################################################\n") if $verbose >= 1;

	$test_protocol = $1;

	if (! defined $SCAN_ARCH{"$test_protocol"}) {
	    print ("define Scan Architecture Hash for \"$test_protocol\"\n") if $verbose >= 1;

	    # initialize @SCAN_ARCH
	    #
	    #$SCAN_ARCH{"$test_protocol"}{"chains"} = ();
	}	   
    }
    # DRC End
    #
    elsif (/^\s*DRC Summary Report$/ and $drc_active) {
	   $drc_active = 0;
    }

    ####################################################################################
    # Detect Fault Model
    ####################################################################################

    # Fault Model Begin
    #
    elsif (/^\s*RM-Info: Running script .*\/(test_.*_atpg).tcl$/) {
	   $atpg_active      = 1;

	   print ("########################################################################\n") if $verbose >= 1;
	   print ("LOGFILE: $_\n")                                                              if $verbose >= 1;
	   print ("########################################################################\n") if $verbose >= 1;
	   	   
	   $fault_model = $1;

	   if (! defined $FAULT_MODEL{"$fault_model"}) {
	       print ("define Fault Model Hash for \"$fault_model\"\n") if $verbose >= 1;
	       my @fault_sim_data    = ();
	       my @atpg_run_data     = ();

	       # initialize @FAULT_MODEL
	       #
	       $FAULT_MODEL{"$fault_model"}{"name"}              = "";
	       $FAULT_MODEL{"$fault_model"}{"test_coverage"}     = "0";
	       $FAULT_MODEL{"$fault_model"}{"fault_coverage"}    = "0";
	       $FAULT_MODEL{"$fault_model"}{"slack_based"}       = "no";
	       $FAULT_MODEL{"$fault_model"}{"test_cycles"}       = "0";
	       $FAULT_MODEL{"$fault_model"}{"test_cycles_total"} = "0";
	       $FAULT_MODEL{"$fault_model"}{"patterns"}          = "0";
	       $FAULT_MODEL{"$fault_model"}{"patterns_total"}    = "0";
	       $FAULT_MODEL{"$fault_model"}{"fault_sim_data"}    = \@fault_sim_data;
	       $FAULT_MODEL{"$fault_model"}{"atpg_run_data"}     = \@atpg_run_data;
	       $FAULT_MODEL{"$fault_model"}{"fault_sim_data"}    = \@fault_sim_data;
	       $FAULT_MODEL{"$fault_model"}{"atpg_run_data"}     = \@atpg_run_data;
	   }
    }
    
    # Fault Model End
    #
    elsif (/^\s*RM-Info: Completed script .*\/(test_.*_atpg).tcl$/ and $atpg_active) {
	   $atpg_active = 0;

	   # calculate total cycle and pattern count
	   $atpg_cycles_total   += $FAULT_MODEL{"$fault_model"}{"test_cycles"};
	   $atpg_patterns_total += $FAULT_MODEL{"$fault_model"}{"patterns"};
	   $FAULT_MODEL{"$fault_model"}{"test_cycles_total"} = $atpg_cycles_total;
	   $FAULT_MODEL{"$fault_model"}{"patterns_total"}    = $atpg_patterns_total;
	   
	   # calculate total fault count
	   foreach $n (keys %{$FAULT_MODEL{"$fault_model"}{"faults"}}) {
	       $atpg_faults_total{$n}+=$FAULT_MODEL{$fault_model}{faults}->{$n};
	       $FAULT_MODEL{"$fault_model"}{"faults_total"}{$n} = $atpg_faults_total{$n};
	   }

	   # calculate total coverage
	   if ($total_cov >= 1) {
	       $FAULT_MODEL{"$fault_model"}{"test_coverage_total"} = calc_TC ($FAULT_MODEL{$fault_model}{faults_total});
	   } else {
	       $FAULT_MODEL{"$fault_model"}{"test_coverage_total"} = "-";
	   }

	   # Verbose Print of @FAULT_MODEL
	   print ("Name                 : $FAULT_MODEL{$fault_model}{name}               \n") if $verbose >= 1;
	   print ("Test Coverage        : $FAULT_MODEL{$fault_model}{test_coverage}      \n") if $verbose >= 1;
	   print ("Test Coverage (Total): $FAULT_MODEL{$fault_model}{test_coverage_total}\n") if $verbose >= 1;
	   print ("Fault Coverage       : $FAULT_MODEL{$fault_model}{fault_coverage}     \n") if $verbose >= 1;
	   print ("Slack Based          : $FAULT_MODEL{$fault_model}{slack_based}        \n") if $verbose >= 1;
	   print ("Test Cycles          : $FAULT_MODEL{$fault_model}{test_cycles}        \n") if $verbose >= 1;
	   print ("Test Cycles (Total)  : $FAULT_MODEL{$fault_model}{test_cycles_total}  \n") if $verbose >= 1;
	   print ("Pattern Count        : $FAULT_MODEL{$fault_model}{patterns}           \n") if $verbose >= 1;
	   print ("Pattern Count (Total): $FAULT_MODEL{$fault_model}{patterns_total}     \n") if $verbose >= 1;
	   foreach $n (keys%{$FAULT_MODEL{"$fault_model"}{"faults_total"}}) {
	       print ("Faults $n            : $FAULT_MODEL{$fault_model}{faults}{$n}\n") if $verbose >= 1;
	       print ("Faults $n(Total)     : $FAULT_MODEL{$fault_model}{faults_total}{$n}\n") if $verbose >= 1;
	   }

	   print ("LOGFILE: $_\n") if $verbose >= 1;

	   my $name = "$FAULT_MODEL{$fault_model}{name}";
	   $name =~ s/\..*//;
	   if ($name ne "") {	  
	       $FAULT_MODEL{"$name"} = delete ($FAULT_MODEL{$fault_model});
	   }
    }
    
    ####################################################################################
    # Begin Scan Architecture Analysis
    ####################################################################################
    if ($drc_active) {
        
	###############################################################################
	# Detect CHAIN length
	###############################################################################
 
	if (/^\s(Chain \d*) successfully traced with (\d*) scan_cells.$/) {
	    $SCAN_ARCH{"$test_protocol"}{"chains"}{$1} = $2;
	    print ("LOGFILE: $_\n") if $verbose >= 1;
	}	
    }


    ####################################################################################
    # Begin Fault Model Analysis
    ####################################################################################
    if ($atpg_active) {
        
	###############################################################################
	# Detect Fault Simulation
	###############################################################################

	if (/^\s*Starting.*fault simulation.*/) {
	    $fault_sim = 1;
	    $atpg_run  = 0;
	    print ("LOGFILE: $_\n") if $verbose >= 1;
	}	

	elsif (/^\s*Fault simulation completed/) {
	    $fault_sim = 0;
	    $atpg_run  = 0;
	    print ("LOGFILE: $_\n") if $verbose >= 1;
	}
	

	###############################################################################
	# Detect ATPG Run
	###############################################################################

	elsif (/^\s*Starting.*ATPG.*/) {
	    $fault_sim = 0;
	    $atpg_run  = 1;
	    print ("LOGFILE: $_\n") if $verbose >= 1;
	}	

	###############################################################################
	# Detect Uncollapsed Summary Report
	###############################################################################

	elsif (/^\s*Uncollapsed/ and /Fault Summary Report$/) {
	    $fault_sim = 0;
	    $atpg_run  = 0;
	    my %FAULTS;
            $FAULT_MODEL{"$fault_model"}{"faults"} = \%FAULTS;
	    print ("LOGFILE: $_\n") if $verbose >= 1;
	}
    

	###############################################################################
	# Detect Faults Counts (out of summary report)
	###############################################################################

	elsif (/.*\s+([A-Z]{2})\s+\(*?(\d+).*/) {
	    $FAULT_MODEL{"$fault_model"}{"faults"}->{$1} = $2;
	    print ("LOGFILE: $_\n") if $verbose >= 1;
	}
    

	###############################################################################
	# Detect internal Pattern File Name
	###############################################################################
	
	elsif (/^\s*End writing file \'(.*)\.bin\.gz\' with ([0-9]+) patterns.*$/) {
            my $name = $1;
	    # extract fault model name
            $name =~ s/$design_name\_//;

	    $FAULT_MODEL{"$fault_model"}{"name"} = "$name";
	    print ("LOGFILE: $_\n") if $verbose >= 1;
	}


	################################################################################
	# Determine Column for Pattern Count and Coverage values
	################################################################################
	
	elsif (/coverage\s+CPU time/ and $atpg_active) {


	    #default values
	    $test_cov_column = 0;
	    $test_cnt_column = 0;

	    for (my $i=0; $i<=$#column; $i++) {
		if      ($column[$i] eq "coverage") {$test_cov_column = $i;}
		elsif ($column[$i] =~ /total/)    {$test_cnt_column = $i;}
	    }
	    
	    #Pattern Count for fault sim is always expected in column=0
	    if ($fault_sim) {
		$test_cnt_column = 0;
	    }
	    print ("LOGFILE: $_\n") if $verbose >= 1;
	    print ("COVERAGE: column=$test_cov_column\n") if $verbose >= 1;
	    print ("PATTERN : column=$test_cnt_column\n") if $verbose >= 1;
	}

	################################################################################
	# Get Pattern Count and Coverage Values
	################################################################################
	
	elsif ($column[$test_cov_column] =~ /\%/ and $atpg_active) {
	    $column[$test_cov_column] =~ s/\%//;

	    ##############################################
	    # Fault Simulation
	    ##############################################
	    if ($fault_sim) {
	        print ("FAULT_SIM_DATA: $column[$test_cnt_column] $column[$test_cov_column]\n") if $verbose >= 1;
		push (@{$FAULT_MODEL{"$fault_model"}{"fault_sim_data"}}, "$column[$test_cnt_column] $column[$test_cov_column]");
	    }

	    ##############################################
	    # ATPG Run
	    ##############################################
	    elsif ($atpg_run) {
	        print      ("ATPG_RUN: $column[$test_cnt_column] $column[$test_cov_column]\n") if $verbose >= 1;
		push (@{$FAULT_MODEL{"$fault_model"}{"atpg_run_data"}}, "$column[$test_cnt_column] $column[$test_cov_column]");
	    }
	    
	}       


    ################################################################################
    # Get Final Values from "Uncollapsed Fault Summary Report"
    ################################################################################

	##############################################
	# Detect Test Cycle Number
	##############################################
	
	elsif (/^.*generating ([0-9]*) test cycles$/) {
	    $FAULT_MODEL{"$fault_model"}{"test_cycles"} = "$1";
	    print ("LOGFILE: $_\n") if $verbose >= 1;
	}

	##############################################
	# Detect Slack Based
	##############################################
	
	elsif (/^.*slackdata_for_atpg=([a-z]*),.*/) {
	    $FAULT_MODEL{"$fault_model"}{"slack_based"} = "$1";
	    print ("LOGFILE: $_\n") if $verbose >= 1;
	}

	elsif (/Slack data will be ignored/) {
	    $FAULT_MODEL{"$fault_model"}{"slack_based"} = "no";
	    print ("LOGFILE: $_\n") if $verbose >= 1;
	}

	##############################################
	# Detect Total Faults
	##############################################
	
	elsif (/^\s*total faults\s+(.*)$/) {
	    $FAULT_MODEL{"$fault_model"}{"faults"}->{ALL} = "$1";
	    print ("LOGFILE: $_\n") if $verbose >= 1;
	}

	##############################################
	# Detect Final Test Coverage
	##############################################
	
	elsif (/^\s*test coverage\s+(.*)\%$/) {
	    $FAULT_MODEL{"$fault_model"}{"test_coverage"} = "$1";
	    print ("LOGFILE: $_\n") if $verbose >= 1;
	}

	##############################################
	# Detect Final Fault Coverage
	##############################################
	
	elsif (/^\s*fault coverage\s+(.*)\%$/) {
	    $FAULT_MODEL{"$fault_model"}{"fault_coverage"} = "$1";
	    print ("LOGFILE: $_\n") if $verbose >= 1;
	}

	##############################################
	# Detect Final Pattern Count
	##############################################
	
	elsif (/^\s*\#internal patterns\s+([0-9]+)$/) {
	    $FAULT_MODEL{"$fault_model"}{"patterns"} = "$1";
	    print ("LOGFILE: $_\n") if $verbose >= 1;
	}


    ####################################################################################
    # End Fault Model Analysis
    ####################################################################################

    }
    else {
	#clear variables
	$test_cov_column     = 0;
	$test_cnt_column     = 0;
			     
	$fault_sim           = 0;		     
	$atpg_run            = 0;

	close(FAULT_SIM);
	close(ATPG_RUN);
   }
}
print ("########################################################################\n") if $verbose >= 1;


#########################################################################################################
# Output Summary Report
#########################################################################################################

print ("---------------------------------------------------------------------------------------------------------------\n");
	   foreach $spf (keys %SCAN_ARCH)   {
	       print ("Test Protocol: $spf\n");
	       print ("---------------------------------------------------------------------------------------------------------------\n");

	       foreach $chain (sort keys %{$SCAN_ARCH{"$spf"}{"chains"}})   {
	       	   print ("$chain: $SCAN_ARCH{$spf}{chains}{$chain} scan_cells\n");
	       }
	   }
print ("---------------------------------------------------------------------------------------------------------------");
print ("------------") if $total_cov >= 1;
print ("\n");
printf ("%-20s", "Fault Model");
printf ("%-12s", "Patterns");
printf ("%-12s", "Patterns");
printf ("%-16s", "Test Cycles");
printf ("%-16s", "Test Cycles");
printf ("%-12s", "Coverage");
printf ("%-12s", "Coverage") if $total_cov >= 1;
printf ("%-12s", "Coverage");
printf ("%-12s", "SlackBased");
print  ("\n");
printf ("%-20s", "");
printf ("%-12s", "");
printf ("%-12s", "(Total)");
printf ("%-16s", "");
printf ("%-16s", "(Total)");
printf ("%-12s", "(Test)");
printf ("%-12s", "(Total)") if $total_cov >= 1;
printf ("%-12s", "(Fault)");
printf ("%-12s", "");
print  ("\n");
print ("---------------------------------------------------------------------------------------------------------------");
print ("------------") if $total_cov >= 1;
print ("\n");

 foreach my $fault_model (sort { $FAULT_MODEL{$a}{patterns_total} <=> $FAULT_MODEL{$b}{patterns_total} } keys%FAULT_MODEL) { #keys %FAULT_MODEL) {
    if ($FAULT_MODEL{$fault_model}{patterns} > 0) {
	printf ("%-20s", "$fault_model");
	printf ("%-12s", "$FAULT_MODEL{$fault_model}{patterns}");
	printf ("%-12s", "$FAULT_MODEL{$fault_model}{patterns_total}");
	printf ("%-16s", "$FAULT_MODEL{$fault_model}{test_cycles}");
	printf ("%-16s", "$FAULT_MODEL{$fault_model}{test_cycles_total}");
	printf ("%-12s", "$FAULT_MODEL{$fault_model}{test_coverage}"."%");
	printf ("%-12s", "$FAULT_MODEL{$fault_model}{test_coverage_total}"."%") if $total_cov >= 1;
	printf ("%-12s", "$FAULT_MODEL{$fault_model}{fault_coverage}"."%");
	printf ("%-12s", "$FAULT_MODEL{$fault_model}{slack_based}");
	print  ("\n");
    } else {
	print  ("WARNING: Could not find ATPG data for \"$fault_model\.tcl\"\n");
	delete ($FAULT_MODEL{$fault_model});
    }
}
print ("---------------------------------------------------------------------------------------------------------------");
print ("------------") if $total_cov >= 1;
print ("\n");


#########################################################################################################
# Generate gnuplot 
#########################################################################################################

if ($gnu_plot) {
    print ("########################################################################\n") if $verbose >= 1;


    ####################################################################################################
    # Generate .dat files with "pattern count" and "coverage value"
    ####################################################################################################
    
    foreach my $fault_model (sort { $FAULT_MODEL{$a}{patterns_total} <=> $FAULT_MODEL{$b}{patterns_total} } keys%FAULT_MODEL) { #( keys %FAULT_MODEL ) {
	if ($FAULT_MODEL{$fault_model}{patterns} > 0) {
	    print ("--------------------------------------------------\n") if $verbose >= 1;
	    print ("$fault_model                                      \n") if $verbose >= 1;
	    print ("--------------------------------------------------\n") if $verbose >= 1;
	    my $fault_dir = "$folder/$fault_model";
	    system ("mkdir -p $fault_dir");
	    
	    my $fault_sim_dat = "$fault_dir/$FAULT_MODEL{$fault_model}{name}"."_fault_sim.dat";
	    print ("open $fault_sim_dat and start with pattern count=0\n") if $verbose >= 1;
	    open(FAULT_SIM,">$fault_sim_dat");
	    
	    print FAULT_SIM ("0 0\n");
	    my $last_cnt = "0";
	    foreach (@{$FAULT_MODEL{"$fault_model"}{"fault_sim_data"}}) {
		if (/(.*) (.*)/) { 
		    print FAULT_SIM ("$1 $2\n");
		    $last_cnt = $1;
		}
	    }
	    
	    my $atpg_run_dat = "$fault_dir/$FAULT_MODEL{$fault_model}{name}"."_atpg_run.dat";
	    print ("open $atpg_run_dat and start with pattern count=$last_cnt\n") if $verbose >= 1;
	    open(ATPG_RUN,">$atpg_run_dat");
	    
	    foreach (@{$FAULT_MODEL{"$fault_model"}{"atpg_run_data"}}) {
		if (/(.*) (.*)/) {
		    printf ATPG_RUN ("%e %e\n", ($1+$last_cnt), $2);
		}
	    }
	}
    }

    ####################################################################################################
    # Create gnuplot script
    ####################################################################################################
    
    print ("########################################################################\n") if $verbose >= 1;
    foreach my $fault_model (sort { $FAULT_MODEL{$a}{patterns_total} <=> $FAULT_MODEL{$b}{patterns_total} } keys%FAULT_MODEL) { #( keys %FAULT_MODEL ) {
	my $name = "$FAULT_MODEL{$fault_model}{name}";
	$name =~ s/\..*//;

	print ("GNUPLOT: generating script for \"$fault_model\"\n") if $verbose >= 1;
	open(GPTOUT,">$folder/$fault_model/$FAULT_MODEL{$fault_model}{name}".".gpt");
	print GPTOUT "set terminal png font \",10\" size 1024,768\n";
	print GPTOUT "set output \"./$FAULT_MODEL{$fault_model}{name}".".png\"\n";
	print GPTOUT "set title \"$fault_model coverage ($logfile)\"\n";
	print GPTOUT "set xlabel \"Pattern Count\"\n";
	print GPTOUT "set ylabel \"Coverage\"\n";
	print GPTOUT "set ytics 5\n";
	print GPTOUT "set key right bottom\n";
	print GPTOUT "set grid ytics lc rgb \"#bbbbbb\" lw 1 lt 0\n";
	print GPTOUT "set grid xtics lc rgb \"#bbbbbb\" lw 1 lt 0\n";
	print GPTOUT "set yrange [0:100]\n";
	print GPTOUT "plot \\\n";	
	print GPTOUT ("\"$FAULT_MODEL{$fault_model}{name}"."_fault_sim.dat\" with lines title \"\", \\\n");
	print GPTOUT ("\"$FAULT_MODEL{$fault_model}{name}"."_atpg_run.dat\" with lines title \"new pattern\"\n");

	close(GPTOUT);
    }


    #####################################################################################################
    # Execute gnuplot script to generate coverage chart (png)
    #####################################################################################################

    print ("########################################################################\n") if $verbose >= 1;
    foreach my $fault_model (sort { $FAULT_MODEL{$a}{patterns_total} <=> $FAULT_MODEL{$b}{patterns_total} } keys%FAULT_MODEL) { #( keys %FAULT_MODEL ) {
    	print ("GNUPLOT: executing \"$fault_model".".gpt\" to generate coverage chart \"$FAULT_MODEL{$fault_model}{name}".".png\"\n") if $verbose >= 1;
    	system ("cd $folder/$fault_model; gnuplot $FAULT_MODEL{$fault_model}{name}".".gpt");
    }


#########################################################################################################
# Generate HTML coverage page
#########################################################################################################

    my $first_fault_model = (sort { $FAULT_MODEL{$a}{patterns_total} <=> $FAULT_MODEL{$b}{patterns_total} } keys%FAULT_MODEL)[0];
    open(HTMLOUT,">$folder/index.html");

    print ("########################################################################\n") if $verbose >= 1;

print HTMLOUT <<EOF;
<head>
  <title>ATPG Coverage</title>
</head>

<script type=\"text/javascript\">
var imgs = [
[],
EOF

    foreach my $fault_model (sort { $FAULT_MODEL{$a}{patterns_total} <=> $FAULT_MODEL{$b}{patterns_total} } keys%FAULT_MODEL) {
	print ("HTML: generating coverage chart for \"$fault_model\"\n") if $verbose >= 1;
	print HTMLOUT "[\"$fault_model/$FAULT_MODEL{$fault_model}{name}".".png\"],\n";
    }

print HTMLOUT <<EOF;
];

function showImg (imgIndex) {
  document.getElementById('img1').src = imgs[imgIndex] ;
  }
</script>

<style type="text/css"  style="justify-content:center"> 
img{width:1024px;height:768px;border:0;} 
.center {
  display: block;
  margin-left: auto;
  margin-right: auto;
}
</style>

<br>
<img id="img1" src="$first_fault_model/$FAULT_MODEL{$first_fault_model}{name}.png" class="center">
<br>
<br>

<div class="wrapper" style="text-align:center">

EOF

my $i=0;
foreach my $fault_model (sort { $FAULT_MODEL{$a}{patterns_total} <=> $FAULT_MODEL{$b}{patterns_total} } keys%FAULT_MODEL) {
    my $name = "$FAULT_MODEL{$fault_model}{name}";
    $name =~ s/\..*//;
    $i++;
    print HTMLOUT "  <input type=\"button\" value=\"$name\" onclick=\"showImg($i)\">\n";
}

    print HTMLOUT <<EOF;
</div>
<br>

EOF


# open HTML coverage overview
#	
    if ($quiet==0) {
	system ("firefox -width 1080 -height 1000 $folder/index.html&");
    }

}



exit;

#########################################################################################################
# Calculate Coverage
#########################################################################################################

sub calc_TC()
{
    if ($_[0]->{ALL} ne "") {
	return sprintf("%2.2f", ($_[0]->{DT} + $_[0]->{PT} * 0.5) / ($_[0]->{ALL} - $_[0]->{UD}) * 100);
    } 
}


#########################################################################################################
# HELP
#########################################################################################################
	
sub usage()
{
    print STDERR <<EOF;
    
    This program does...
	
      usage: $0 [-hvpq] [-l <file>] [-r <dir>]
      
      Required:
      -l <logfile>     : atpg log file

      Optional:
      -p               : generates a html coverage chart/plot
      -r <directory>   : specifies the reports directory (default: ./reports/coverage)
      -h               : this (help) message
      -v               : verbose output
      -q               : do not open firefox to display the plots

    example: $0 -f logs/tmax_output.comp.log
EOF
exit;
}
