#!/usr/bin/perl -w
#############################################################################
# File:           create_lof.pl
#
# Summary:        parsing the files.f in folder results and compose the content of
# 				  the given files.f to a file with name digital.f for vivado
#
# Author:         Markus Winkler
# E-Mail:         markus.winkler@dmos2002.de
# Org:            DMOS GmbH
#
# Description:
#
#############################################################################

use strict;
use Getopt::Std;

my $file     = "./results/files.f";
my @lines    = ();
my @newlines = ();
my @rtllines = ();
my @inclines = ();
my %hash = ();

# read in files.f and store content in @lines
open( FILE, "<$file" ) || die "File $file not found";
@lines = <FILE>;
close(FILE);

# @lines contents paths to other files.f
# so we process @lines line for line and read in the content of the given files.f
# and store this in @newlines
foreach (@lines) {
	print "Reading $_";
	open( FILE, "<$_" ) || die "File $_ not found";
	push( @newlines, <FILE> );
	close(FILE);
}

push( @rtllines, "+incdir+../../config\n" );
push( @rtllines, "+incdir+../../edf_registers\n" );
push( @rtllines, "+incdir+../../ECC/rtl\n" );
push( @rtllines, "+incdir+../../STD_COMPONENTS/inc\n" );
push( @rtllines, "+incdir+../../DSI3_MASTER/rtl\n" );

# Now we pick out of @newlines all packages and store them only once in @rtllines
foreach (@newlines) {
	;    # At first process packages
	if ( $_ =~ m/^(\/\/)|""/ ) { }; # Ignoring commented and whitspace lines
	if ( $_ =~ m/^(\$\{?DESIGN\}?\/\$\{?DIGITAL\}?)(.*_pkg.sv)/ ) {
		#%hash = map{$2,1}@rtllines; #sorting out double entries
		print "\tAdding package file ../..$2\n";
		push( @rtllines, "../..$2\n" );
	}
	if ( $_ =~ m/^(\$\{?DESIGN\}?\/\$\{?DIGITAL\}?)(.*_pkg.vhd)/ ) {
		#%hash = map{$2,1}@rtllines; #sorting out double entries
		print "\tAdding vhdl package file ../..$2\n";
		push( @rtllines, "../..$2\n" );
	}
}

print "\tAdding file ../../tech/TSMC_180_BCD/ip/ROM_Nibble/models/tcb018gbwp7t_rom.v to digital.f\n";
push( @rtllines, "../../tech/TSMC_180_BCD/ip/ROM_Nibble/models/tcb018gbwp7t_rom.v\n" );

# Now we pick out all deign files excluding string "_pkg" and push them after the packages to @rtllines
foreach (@newlines) {
	;    # At second process rtl files
	if ( $_ =~ m/^(\/\/)|""/ ) { }; # Ignoring commented and whitspace lines
	if ( $_ =~ m/^(\$\{?DESIGN\}?\/\$\{?DIGITAL\}?)(?!.*_pkg.*)(.*v.*)/) {
		print "\tAdding file ../..$2\n";
		push( @rtllines, "../..$2\n" );
	}
}

@newlines = ();

#write out the content of @rtllines to new digital.f in folder results
open( FILE, ">./results/digital.f" )
  || die "File digital.f cannot be opened for write";
print FILE @rtllines;
close(FILE);
print "Finished creating digital.f\n";

1;
