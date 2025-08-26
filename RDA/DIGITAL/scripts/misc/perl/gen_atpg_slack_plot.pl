#!/usr/bin/perl

############################################################################################
# (C) COPYRIGHT 2020 ELMOS Semiconductor SE
# ALL RIGTHS RESERVED
#
# Date:   2021-09-23
# Author: MAKOE
#
# Info: This Script is intended to parse the tetramax slack report file and to extract
#       the all values to generate a graph for "tmgn", "tdet" and "delta".
#
#       Generated files
#       --------------------------------------------------------------------------------
#       <dir>
#            |/<type>_[hist|dist].dat (containing timing values and fault counts)
#            |/<type>_[hist|dist].gpt (gnuplot script to generate graphs)
#            |/<type>_[hist|dist].png (graph as png)
#            |/index.html             (HTML Page to show all results)
# 
############################################################################################


############################################################################################
# analyze script arguments
############################################################################################
use Getopt::Std;
my $opt_string = 'qhr:';
getopts( "$opt_string", \%opt ) or usage();
usage() if $opt{h};

# do not open firefox
#
my $quiet = "$opt{q}";

# define file to be parsed {-f <file>}
#
my $report = "$opt{r}";
my $folder  = $report;
   $folder  =~ s/\..*//;

system ("mkdir -p $folder");

############################################################################################
# common variables
############################################################################################

my $type          = 0;
my @sorted_types  = ();

############################################################################################
# parse report/logfile
############################################################################################

open(INPUT, $report) or usage();

while (<INPUT>) {
    chomp ($_);

    ####################################################################################
    # Detect Histogram
    ####################################################################################

    if (/^\s*Histogram of Uncollapsed Fault Distribution$/) {
	$type   = "";
    }
    elsif (/^\s*(\w+)\s*$/ & ($type eq "")) {
	$type = "$1"."_hist";
	push (@sorted_types, $type); 
        open(DATA,">$folder/$type.dat");
    }    
    elsif (/^\s*(\d+\.\d+)\s*-\s*(\d+\.\d+):\s*(\d+)/) {
	print DATA ("$1 $3\n");
    }	
    elsif (/^\s*>\s*(\d+\.\d+):\s*(\d+)/) {
	print DATA ("$1 0\n");
	close (DATA);
    }		

    ####################################################################################
    # Detect Cumulative Distribution
    ####################################################################################

    elsif (/^\s*Cumulative Distribution of (.*)$/) {
	$type = "$1"."_dist";
	push (@sorted_types, $type); 
        open(DATA,">$folder/$type.dat");
    }
    elsif (/^\s*(\d+\.\d+):\s*(\d+)/) {
	print DATA ("$1 $2\n");
    }	
    elsif (/^\s*< inf:\s*(\d+)/) {
	close (DATA);
    }		

}

#############################################################################################
# Combine tmgn and tdet if both are available 
#############################################################################################

@sorted_types = ("tmgn_tdet_hist", "delta_hist", "tmgn_tdet_dist", "delta_dist");

# to be done!!!!!!
#foreach $type (@sorted_types) {
#}

#############################################################################################
# Generate gnuplot 
#############################################################################################

foreach my $type (@sorted_types) {
    my @types      = split (/_/,$type);
    pop (@types);
    my $first_type = shift (@types);

    open(GPTOUT,">$folder/$type.gpt");
    print GPTOUT "set terminal png font \",10\" size 1024,768\n";
    print GPTOUT "set output \"./$folder/$type.png\"\n";
    print GPTOUT "set ylabel \"Faults\"\n";
    print GPTOUT "set xtics rotate\n";
    print GPTOUT "set xtics offset -1,0\n";

    if ($type =~ /delta/) {print GPTOUT "set xlabel \"Delta\"\n";}
    else                  {print GPTOUT "set xlabel \"Slack\"\n";}

    #########################################################################################
    # Histograms
    #########################################################################################
    if ($type =~ /(.*)_hist/) {
	print GPTOUT "set style data histograms\n";
	print GPTOUT "set style fill solid\n";
	print GPTOUT "set title \"Histogram of Uncollapsed Fault Distribution ($report)\"\n";

                          print GPTOUT "plot \"$folder/$first_type"."_hist.dat\" using 2:xtic(1) title \"$first_type\"";	
	foreach (@types) {print GPTOUT    ", \"$folder/$_"."_hist.dat\" using 2:xtic(1) title \"$_\"";}
    }
    #########################################################################################
    # Cumulative Distribution 
    #########################################################################################
    else {
	print GPTOUT "set title \"Cumulative Fault Distribution\"\n";

                          print GPTOUT "plot \"$folder/$first_type"."_dist.dat\" with lines title \"$first_type\"";	
	foreach (@types) {print GPTOUT    ", \"$folder/$_"."_dist.dat\" with lines title \"$_\"";}
    }

    close(GPTOUT);
    
    system ("gnuplot $folder/$type.gpt");
}

#############################################################################################
# Generate HTML coverage page
#############################################################################################

open(HTMLOUT,">$folder/index.html");

print HTMLOUT <<EOF;

<head>
  <title>ATPG Slack Histogram</title>
</head>

<script type=\"text/javascript\">
var imgs = [
[],
EOF

foreach my $type (@sorted_types) {
    print HTMLOUT "[\"$type.png\"],\n";
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
<img id="img1" src="$sorted_types[0].png" class="center">
<br>
<br>

<div class="wrapper" style="text-align:center">

EOF

$i = 1;
foreach $type (@sorted_types) {
    my @types = split (/_/,$type);
    pop (@types);
    my $first_type = shift (@types);

    if ($type =~ /hist/) {
	print HTMLOUT "  <input type=\"button\" value=\"Histogram\n$first_type";
    }
    else {
	print HTMLOUT "  <input type=\"button\" value=\"Cummulative\n$first_type";
    }
    foreach (@types) {
	print HTMLOUT " \\ $_";
    }
    print HTMLOUT "\" onclick=\"showImg($i)\">\n";
    $i++;
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
#########################################################################################################
# HELP
#########################################################################################################
	
sub usage()
{
    print STDERR <<EOF;
    
    This program does...
	
      usage: $0 [-hq] [-r <file>]
      
      Required:
      -r <report>     : slack report file

      Optional:
      -h               : this (help) message
      -q               : do not open firefox to display the plots

    example: $0 -f reports/digital_trans_slack_based.comp.rpt
EOF
exit;
}
