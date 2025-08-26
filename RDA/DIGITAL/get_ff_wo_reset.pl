#!/usr/bin/perl -w
#                              -*- Mode: CPerl -*- 
use lib $ENV{'DMOS_TOOLS_DIR'}.'/project/lib';

################################################################################

BEGIN {
  my $cvs = '$Id: gen_ff_wo_reset,v 1.0 2016/01/04 07:38:00 jvoi Exp $ ';
  $cvs =~ /Id: [^,]*,v ([0-9\.]+) ([0-9\/]+)/;
  ($ENV{ 'CVSVERSION' }, $ENV{ 'CVSDATE' }) = ($1, $2);
  $ENV{ '_DESCRIPTION_' } = "LogFile parser for DC";
  $ENV{ '_AUTHOR_' } = 'Jens Voigt';
}

#use strict;
use Project;
use Utils::Program;
use Utils::Output;
use Utils::FileSystem;

my $log_file = shift_argument();
my $signed_fails = "";
my $memory = 0;
my $mem_end = 0;
my $reset_fails = "";
my $file_name = "";
my $reg_header = "     =================================================================================
     |     Register Name     |   Type    | Width | Bus | MB | AR | AS | SR | SS | ST |
     =================================================================================\n";
my $port_removals = "";
my $opt_removals_1206 = "";
my $opt_removals_1207 = "";
my $opt_removals_1215 = "";
my $current_block = "";


unless (-e $log_file) {
  printlog( "calling syntax: " . program_name() . " <log_file>" );
  die( "log file does not exist.\n($log_file)\n" );
}

printlog("reading log file $log_file" );
my @pattern = read_file( $log_file );

print "\n\n################################################################\n";
print "Register without reset";
print $reg_header;

foreach my $line (@pattern) {
	# get file name
	#print "Mem: $memory";
	if ($memory eq 1){
		#print "inside!";
		if ($line =~ /\/projekte\//) {
			#print "File:$line";
			$file_name = "File: $line";
		}
		elsif ($line =~ /(\s*N\s*\|){5,5}$/) {
			$reset_fails = "${reset_fails}Reg: $line"
			#print "Reg: $line";
		}
		elsif ($line =~ /^=+$/) {
			$mem_end++;
			if ($mem_end > 2) {
				$memory = 0;
				$mem_end = 0;
				if ($reset_fails ne "") {
					print $file_name;
					print $reset_fails;
					$reset_fails = "";
				}
			}
		}
	}
	elsif ($line =~ /\(VER-318\)/) {
		$signed_fails = "$signed_fails $line";
	}
	elsif ($line =~ /Inferred memory devices in process/) {
		$memory = 1;
		
	}
	#Removing port 'i_gpr_addr_a[4]' from design 'mutec_regfile_datawidth8_registerfilesize16'
	elsif ($line =~ /^Removing port.*/) {
		$port_removals = "$port_removals$line";
	}
	
	#Information: The register 'motor_amp_h_lim_times_pll_cnt_reg[31]' is a constant and will be removed. (OPT-1206)
	elsif ($line =~ /Information:.*?\(OPT-1206\)/) {
		$opt_removals_1206 = "$opt_removals_1206$line";
	}
	
	#Information: In design 'motor_state_machine', the register 'adc_curr_filt_en_reg' is removed because it is merged to 'en_gsc_dac_ctrl_reg'. (OPT-1215)
	elsif ($line =~ /Information:.*?\(OPT-1215\)/) {
		$opt_removals_1215 = "${opt_removals_1215}$line";
	}
	
	#Information: The register 'i_digtop_intern/i_core/i_pmsm_top/pulse_cnt/cnt_reg[4]' will be removed. (OPT-1207)
	elsif ($line =~ /Information:.*?\(OPT-1207\)/) {
		$opt_removals_1207 = "$opt_removals_1207$line";
	}
	
	#
	
#	elsif ($line =~ /(\s*N\s*\|){5,5}$/) {
#		print "Reg: $line";
#	}
}

print "\n\n################################################################\n";
print "Signed Fails\n";
print $signed_fails;
print "\n\n################################################################\n";
print "Optimizations: Removed registers because it is constant\n";
print $opt_removals_1206;
print "\n\n################################################################\n";
print "Optimizations: Removed registers\n";
print $opt_removals_1207;
print "\n\n################################################################\n";
print "Optimizations: Removed registers because it is merged\n";
print $opt_removals_1215;
print "\n\n################################################################\n";
print "Optimizations: Removed ports\n";
print $port_removals;
