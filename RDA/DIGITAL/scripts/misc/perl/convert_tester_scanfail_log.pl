#!/usr/bin/env perl
use strict;
use warnings;

################# CUSTOMIZE BEGIN #######################################
#deprecated
my $pos_a = 3; # select collum position of first output in log file 
my $pos_b = 7; # select collum position of second output in log file 

#deprecated
my $signal_a = "o_sdo_out[0]"; # name your pins #deprecated
my $signal_b = "o_sdo_out[1]"; # name your pins


## TODO: autodetect stuck or trans on header"
my $header = ".pattern_file_name digtop_stuck.scan.stil\n"; # name your stil file

################# CUSTOMIZE END #######################################

# < HELP ---------------------

if( $ARGV[0] eq '-h' || $ARGV[0] eq '-help' || $ARGV[0] eq "")
{
help();
print_example();
exit;
}


sub help { 
print '

######### HELP ################################
_____________________________
Usage: perl convert_log.pl <input_log_file_from_tester.txt>
     Output is tmax readable Scanfailure format\n
     
     
';
}
sub print_example { 
print '
Example INPUT from tester (LTX): ####################
_____________________________________


PATTERN DEBUG for "STUCK_pattern._flat_seq__st", fails are marked with "X"
Fail Cycles for Site4: 
cycle #	SCKA_FX	SDIA_FX	CSNA_FXHV	SDOA_FX	SCKB_FX	SDIB_FX	CSNB_FXHV	SDOB_FX	RSOA_FX	TXD_FX	
9587	-	-	-	-	-	-	-	X	-	-	
59992	-	-	-	-	-	-	-	X	-	-	
257846	-	-	-	-	-	-	-	X	-	-	
-------------------------------------------------

PATTERN DEBUG for "STUCK_pattern._flat_seq__st", fails are marked with "X"
Fail Cycles for Site4: 
cycle #	SCKA_FX	SDIA_FX	CSNA_FXHV	SDOA_FX	SCKB_FX	SDIB_FX	CSNB_FXHV	SDOB_FX	RSOA_FX	TXD_FX	
9587	-	-	-	-	-	-	-	X	-	-	
257846	-	-	-	-	-	-	-	X	-	-	
274164	-	-	-	-	-	-	-	X	-	-	
-------------------------------------------------


Output will be: ################################
_____________________


.pattern_file_name digtop_stuck.scan.stil
C o_sdo_out[1] 9587
C o_sdo_out[1] 59992
C o_sdo_out[1] 257846


';

}




# -------------------------- HELP >

my $filename_src = $ARGV[0];           # store the 1st argument into the variable
print "reading file $filename_src\n";
open (FH_SRC, '<', "$filename_src") or die "Cannot open file for reading: $filename_src\n $!"; # open the file using lexically scoped filehandle
print "done open file\n";

my $filename_type ="_stuck_";
my $filename_des;
my $file_des_nr = 1;
($filename_des = "${filename_src}${filename_type}${file_des_nr}.diag") =~ s/\.txt//g;

my $file_des_open = 0;
#open (FH_DES, '>', $filename_des) or die $!; # open the file using lexically scoped filehandle




my @signal_names = [];
my @signal_pos   = [];
 
## analyze the log for valid data:
while( my $line_src = <FH_SRC>)  {   
#find somithing like below and detect names
#cycle #	SCKA_FX	SDIA_FX	CSNA_FXHV	SDOA_FX	SCKB_FX	SDIB_FX	CSNB_FXHV	SDOB_FX	RSOA_FX	TXD_FX	
	if ($line_src =~ 'cycle #\s+(([\w\[\]]+\s+)+)') {
		my $names;
		($names = "${line_src}") =~ s/\cycle #\s*//g;
		print "Found names: $names";
		@signal_names = split (/\s+/, $1);
	}
	## find and detect valid failes
	##8449	-	-	-	-	-	-	-	X	-	-	
	if ($line_src =~ '\d+\s+(([-X]\s+)+)') {
		my @positions = split (/\s+/, $1);
		#print join(", ", @positions);
		for my $i (0 .. $#positions){
			if ($positions[$i] eq 'X'){
				$signal_pos[$i] = 1;
				#print "$i\n";
			}
		}
	}
}
print join(", ", @signal_names);
print "\n";
		for my $i (0 .. $#signal_pos){
			if ($signal_pos[$i] == 1){
				print "$i, "
			}
		}
print "\n";

seek FH_SRC, 0, 0;

while( my $line_src = <FH_SRC>)  {   
	# START
	if ($line_src =~ "PATTERN DEBUG for") {
		if ($line_src =~ /stuck/i) {
			$filename_type ="_stuck_"; 
			$header =~ s/trans/stuck/g;
			
		}
		if ($line_src =~ /trans/i) {
			$filename_type ="_trans_";
			$header =~ s/stuck/trans/g;
			print $header;
		}
		if ($file_des_open == 0) {
			($filename_des = "${filename_src}${filename_type}${file_des_nr}.diag") =~ s/\.txt//g;
			print "new Log\n";
			open (FH_DES, '>', $filename_des) or die $!;
			$file_des_open = 1;
			print "$filename_des, $header \n";
			print FH_DES "\n\n";
			print FH_DES $header;

		}
	}
	
	#ENDE
	if ($line_src =~ "^--------------------------------") {
		if ($file_des_open == 1) {
			close FH_DES;
			$file_des_nr++;
			$file_des_open = 0;
			($filename_des = "${filename_src}${filename_type}${file_des_nr}.diag") =~ s/\.txt//g;
		}
	}


# PATTERN
	if ($line_src =~ /^(\d+)\s+(([-X]\s+)+)/) {
		if ($file_des_open == 0) {
			print $line_src;
			exit();
			open (FH_DES, '>', $filename_des) or die $!; # open the file using lexically scoped filehandle
			print FH_DES $header;
		}
		
		my @data = split (/\s+/, $2);
		my $vector = $1;
		
		#foreach (@data) { print "$_"; } print "\n";
#		print "$line_src \n";
		
		for my $i (0 .. $#data){
			if ($data[$i] eq 'X') {
				print        "C ${signal_names[$i]} ${vector}\n";
				print FH_DES "C ${signal_names[$i]} ${vector}\n";
			}	
		}
	}
}
close FH_SRC;
close FH_DES if ($file_des_open == 1);
