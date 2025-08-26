#!/usr/bin/perl -w

use strict;
use Cwd;

open(EPMS, "$ARGV[0]")    || die "Cannot open  \"$ARGV[0]\": $!\n";
#open(OUT, ">$ARGV[1]")  || die "Cannot write \"$ARGV[1]\": $!\n";

our $name  = $1;
our $value = $2;
our $found = 0;
our $fail_counter = 0;
    
#################
#################

sub browse_folders {

  my @files = glob("$_[0]/*");
  
  foreach (@files){
    my $current_file = $_;
    #print "($_)\n";
    
    if ($current_file =~ /\.gpp/i){
     
      open(VA, "$_")  || die "Cannot open  \"$_\": $!\n";
      
      foreach (<VA>){
        if ($_ =~ /$name/){
          $found = 1;
	  #print "\t\t\t$current_file: $_";
	}
      }
      
      close(VA);
     
    }
    browse_folders($current_file);
  }

}

#################
#################

foreach (<EPMS>){
  
  #print "$_";
  
  if ($_ =~ /(epm__\S+)\s+(\S+)/i){
  
    $name = $1;
    eval "\$value = $2";
    $found = 0;
    
    browse_folders($ARGV[1]);
      
    if ($found < 1){
      print "\t\tNot used: $name = $value\n";
      ++$fail_counter;
    }
  
  }
}

print "\n\t--> $fail_counter not used\n\n";

#################
#################

close EPMS;
#close OUT;

#################
#################
