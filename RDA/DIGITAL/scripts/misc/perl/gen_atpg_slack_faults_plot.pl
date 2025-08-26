#!/usr/bin/perl

############################################################################################
# (C) COPYRIGHT 2020 ELMOS Semiconductor SE
# ALL RIGTHS RESERVED
#
# Date:   2021-09-16
# Author: MAKOE
#
# Info: This Script is intended to parse the tetramax fault results and to extract
#       for each fault the expected and detected slack timing.
#
#       Generated files
#       --------------------------------------------------------------------------------
#       <dir>
#            |/slack_cloud.dat (containing timing values and fault counts)
#            |/slack_cloud.gpt (gnuplot script to generate histogram)
#            |/slack_cloud.png (png for histograms)
#            |/index.html      (HTML Page to show all results)
# 
############################################################################################


############################################################################################
# analyze script arguments
############################################################################################
use Getopt::Std;
my $opt_string = 'qhf:';
getopts( "$opt_string", \%opt ) or usage();
usage() if $opt{h};

# do not open firefox
#
my $quiet = "$opt{q}";

# define file to be parsed {-f <file>}
#
my $fault_file = "$opt{f}";
my $folder     = $fault_file;
   $folder     =~ s/\..*//;

system ("mkdir -p $folder");

############################################################################################
# common variables
############################################################################################

my @data = ();
my $report = "slack_cloud";

############################################################################################
# parse report/logfile
############################################################################################

open(INPUT, $fault_file) or usage();
open(OUTPUT, ">$folder/$report.dat") or usage();

while (<INPUT>) {
    chomp ($_);	    
    @data = split (/\s+/,$_);
    if ($data[$#data-1] =~ /^\d/ and $data[$#data] =~ /^\d/) {
    	printf OUTPUT ("%s %s\n", $data[$#data-1], $data[$#data-1]+$data[$#data]);
    }
}

#############################################################################################
# Generate gnuplot 
#############################################################################################

open(GPTOUT,">$folder/$report.gpt");
print GPTOUT "set title \"Slack Correlation Plot ($fault_file)\"\n"; 
print GPTOUT "set terminal png font \",10\" size 1024,768\n";
print GPTOUT "set output \"./$folder/$report.png\"\n";
print GPTOUT "set xlabel \"slack on expected path\"\n";
print GPTOUT "set ylabel \"slack on detected path\"\n";
print GPTOUT "set xrange [0:]\n";
print GPTOUT "set yrange [0:]\n";
print GPTOUT "set grid xtics lt 0 lw 1 lc rgb \"\#000000\"\n";
print GPTOUT "set grid ytics lt 0 lw 1 lc rgb \"\#000000\"\n";
print GPTOUT "plot x lw 3 lt rgb \"green\" title \"expected fault\", \"$folder/$report.dat\" lt rgb \"red\" title \"detected fault\"";	
close(GPTOUT);
system ("gnuplot $folder/$report.gpt");


#############################################################################################
# Generate HTML coverage page
#############################################################################################

open(HTMLOUT,">$folder/index.html");

print HTMLOUT <<EOF;

<head>
  <title>ATPG Slack Correlation</title>
</head>

<script type=\"text/javascript\">
var imgs = [
[],
EOF

print HTMLOUT "[\"$report.png\"],\n";

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
<img id="img1" src="$report.png" class="center">
<br>
<br>

<div class="wrapper" style="text-align:center">

EOF

print HTMLOUT "  <input type=\"button\" value=\"Slack Faults\" onclick=\"showImg(1)\">\n";

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
	
      usage: $0 [-hq] [-f <file>]
      
      Required:
      -f <logfile>     : slack fault file

      Optional:
      -h               : this (help) message
      -q               : do not open firefox to display the plots
    example: $0 -f results/digtop_trans_slack_post.comp.faults
EOF
exit;
}
