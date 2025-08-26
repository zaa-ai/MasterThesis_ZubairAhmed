#!/usr/bin/perl -w

use strict;

my $DESIGN = $ENV{'DESIGN'};
my $DIGITAL = $ENV{'DIGITAL'};

my $crc = 0;
my $crc_line = `fgrep "crc checksum" $DESIGN/$DIGITAL/logs/generate_software_52142.log | egrep -e "0x\\w+" -o`;

print "crc : $crc_line";

if ( $crc_line =~ /0x(\w+)/ ) {#
	$crc = $1;
} 
print "crc=$crc\n";
open (my $file,'>', "$DESIGN/$DIGITAL/config/crc.txt" );
print $file "$crc\n";
close $file; 
exit 0;
