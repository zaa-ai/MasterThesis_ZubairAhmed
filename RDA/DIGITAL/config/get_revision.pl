#!/usr/bin/perl -w

my $revision = 0;
##my $result = `svnversion -n`;
my $result = 1

# examples: "930", "930M", "930:934", "930:934M" 
if ( $result =~ /^((\d+):)?(\d+)\w?$/i ) {
	$revision = $3;
} 
print "$revision";

exit 0;
