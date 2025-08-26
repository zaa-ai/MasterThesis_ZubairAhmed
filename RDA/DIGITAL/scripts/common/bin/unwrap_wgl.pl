#!/usr/bin/perl

# ========================================================================== #
# This program is free software: you can redistribute it and/or modify       #
# it under the terms of the GNU General Public License as published by       #
# the Free Software Foundation, either version 3 of the License, or          #
# (at your option) any later version.                                        #
#                                                                            #
# This program is distributed in the hope that it will be useful,            #
# but WITHOUT ANY WARRANTY; without even the implied warranty of             #
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the              #
# GNU General Public License for more details.                               #
#                                                                            #
# You should have received a copy of the GNU General Public License          #
# along with this program.  If not, see <http://www.gnu.org/licenses/>.      #
#                                                                            #
# Dieses Programm ist Freie Software: Sie können es unter den Bedingungen    #
# der GNU General Public License, wie von der Free Software Foundation,      #
# Version 3 der Lizenz oder (nach Ihrer Wahl) jeder neueren                  #
# veröffentlichten Version, weiterverbreiten und/oder modifizieren.          #
#                                                                            #
# Dieses Programm wird in der Hoffnung, dass es nützlich sein wird, aber     #
# OHNE JEDE GEWÄHRLEISTUNG, bereitgestellt; sogar ohne die implizite         #
# Gewährleistung der MARKTFÄHIGKEIT oder EIGNUNG FÜR EINEN BESTIMMTEN ZWECK. #
# Siehe die GNU General Public License für weitere Details.                  #
#                                                                            #
# Sie sollten eine Kopie der GNU General Public License zusammen mit diesem  #
# Programm erhalten haben. Wenn nicht, siehe <http://www.gnu.org/licenses/>. #
# ========================================================================== #

##############################################################################
# Author        : Andreas Wiener
# Date          :
#
# Category      : Design Flow
# Project       :
#############################################################################

use strict;
use warnings;

use Switch;
use Term::ANSIColor;

if (@ARGV > 2) {die "Check Command Line Parameters.\n"};

my $filename     = shift;  # get 1st command line entry (input file name)
my $otype_option = shift;  # get 2nd command line entry (output type  : "wgl"=single flat WGL file, "pat"=multiple pattern files)
my $debug_option = shift;  # get 3rd command line entry (debug option : "dbg"=debug, "dbg_c"=colored debug, ""=no debug)

my $debug = 0;

my $subroutine_ref;
my $pattern_ref;
my $vector_nr;
my $timeplate_ref;
my $signals_ref;
my $waveform_name;

#############################################################################
# Main Program
#############################################################################

($pattern_ref, $subroutine_ref, $timeplate_ref, $signals_ref)=&PARSE_WGL($filename);

switch ($debug_option) {
  case "dbg" {
    $debug=1;
    &INFO_PRINT( "DEBUG ENABLED\n", 1);
  }
  case "dbg_c" {
    $debug=2;
    &INFO_PRINT( "COLOR DEBUG ENABLED\n", 2);
  }
  else {
    $debug=0;
    &INFO_PRINT( "Normal Output\n", 0);
  }
}

switch ($otype_option) {
  case "pat" {
    &UNWRAP_TO_MULTI_PAT($pattern_ref, $subroutine_ref, $timeplate_ref, $signals_ref, $debug);
  }
  case "swgl" {
    &UNWRAP_TO_SINGLE_WGL($pattern_ref, $subroutine_ref, $timeplate_ref, $signals_ref, $debug);
  }
  case "mwgl" {
    &UNWRAP_TO_MULTI_WGL($pattern_ref, $subroutine_ref, $timeplate_ref, $signals_ref, $debug);
  }
}

exit(0);

#############################################################################
# Subroutines
#############################################################################
# ---------------------------
sub PARSE_WGL{
# ---------------------------
  my ($file)=@_;

  my $line;
  my $name;
  my $comment = "";

  my %pattern_hash;
  my $found_pattern=0;
  my %subroutine_hash;
  my $found_subroutine=0;
  my @timeplate_arr;
  my $found_timeplate=0;
  my @signals_arr;
  my $found_signals=0;

  my $found_loop=0;
  my $loop_level=0;

  my @loop_count;
  my @loop_calls;

  # open filename
  if ($file eq "") {
    die "Filename not found\n"
  }
  else {
    open(IN, "<$file") || die("ERROR: cannot open file \"$file\" for read !\n");
  }

  while(<IN>) {
    chomp;
    $line=$_;
    $line=~ s/\t/ /g; # substitute tab with space
    $line=~ s/\s*$//; # substitute tab with space

    if ( ( $line !~ m/^\s*$/ ) && ( $line !~ m/^\s*#/ ) ){
      if (( $line =~ m/^\s*call/ ) || ( $line =~ m/^\s*vector/ ) ){
        if ( $line !~ m/;\s*$/ ) {
          print STDERR "WARN : Missing ';' on end of line in input file on line $.\n";
        }
      }

      if ( $line =~ m/^\s*end\s*$/ ) {
        if ( $found_loop == 1) {
          for my $i (1..$loop_count[$loop_level]) {
            foreach my $calls (@{$loop_calls[$loop_level]}) {
              foreach my $call ($calls) {
                if ($loop_level > 1) {
                  push @{$loop_calls[$loop_level-1]},$call;  # push call to lower level calls
                } else {
                  if ( $found_subroutine == 1) {
                    push @{$subroutine_hash{$name}},$call;
                  }
                  if ( $found_pattern == 1) {
                    push @{$pattern_hash{$name}},$call;
                  }
                }
              }
            }
          }

          $loop_count[$loop_level]=1;
          undef($loop_calls[$loop_level]);

          $loop_level--;
          if ($loop_level == 0) {
            $found_loop=0;
          }
        }
        else {
          $found_subroutine=0;
          $found_pattern=0;
          $found_signals=0;
          if ( $found_timeplate == 1) {
            push @timeplate_arr,$line;
            $found_timeplate=0;
          }
        }
      }

      if (( $found_subroutine == 1) or ( $found_pattern == 1)) {
        if ( $line =~ m/^\s*loop\s+([0-9]+)/ ) {
          $loop_level++;
          $found_loop=1;
          $loop_count[$loop_level]=$1;
        }
        elsif ( $line !~ m/\s*end\s*$/ ) {
          $line =~ s/^\s*call\s+(.*)\(\);/$1/;

          if ( $found_loop == 1) {
            push @{$loop_calls[$loop_level]},$line;
          } else {
            if ( $found_subroutine == 1) {
              push @{$subroutine_hash{$name}},$line;
            }
            if ( $found_pattern == 1) {
              push @{$pattern_hash{$name}},$line;
            }
          }
        }
      }

      if ( $found_timeplate == 1) {
        push @timeplate_arr,$line;
      }

      if ( $found_signals == 1) {
        push @signals_arr,$line;
      }

      if ( $line =~ m/^\s*\{(.*)/ ) {
        $comment = "    {subroutine ".$1;
        if (($comment =~ m/subroutine jtag_cycle/) ||
            ($comment =~ m/subroutine jtag_incr_cycle/) ||
            ($comment =~ m/subroutine jtag_w1us_cycle/) ||
            ($comment =~ m/subroutine jtag_w1ms_cycle/)) {
          $comment = "";
        }
      }

      if ( $line =~ m/^\s*subroutine\s+(.*)\(\)/ ) {
        $found_subroutine=1;
        if ( ! exists $subroutine_hash{$name} ) {
          @{$subroutine_hash{$name}} = ();
        }
        $name=$1;
        if ($comment ne "") {
          push @{$subroutine_hash{$name}},$comment;
        }
      }

      if ( $line =~ m/^\s*pattern\s+(.*)\s*$/ ) {
        $found_pattern=1;
        $name=$1;
      }

      if ( $line =~ m/^\s*timeplate\s(.*)\s+(.*)\s+(.*)\s*$/ ) {
        $found_timeplate=1;
        push @timeplate_arr,$line;
      }

      if ( $line =~ m/^\s*signal\s*$/ ) {
        $found_signals=1;
      }

      if ( $line =~ m/^\s*waveform\s*(.*)\s*$/ ) {
        $waveform_name = $1;
      }
    }
  }

  close(IN);
  return (\%pattern_hash, \%subroutine_hash, \@timeplate_arr, \@signals_arr);
}

# ---------------------------
sub UNWRAP_TO_MULTI_PAT {
# ---------------------------
  my $pattern_ref     = shift;
  my %pattern_hash    = %$pattern_ref;

  my $subroutine_ref  = shift;
  my %subroutine_hash = %$subroutine_ref;

  my $timeplate_ref   = shift;
  my $signals_ref     = shift;

  my $outputtype      = shift;

  my $pattern_name;

  foreach my $pattern (keys %pattern_hash) {
    my $file = &EXTRACT_FN($pattern);
    $pattern_name = "asic_".$file;

    &INFO_PRINT("Creating pattern for \"".$pattern."\" in file \"".$file.".pat\"\n", $outputtype);

    open(OUT, ">$file.pat") || die("ERROR: cannot open file \"$file\" for writing !\n");
    &PRINT_HEADER(\*OUT, $pattern_name, $timeplate_ref, $signals_ref);

    print OUT "pattern ".$pattern."\n";

    foreach my $pattern ( @{$$pattern_ref{$pattern}} ) {
      if ( $pattern =~ m/^\s*vector/ ) {
        print OUT $pattern."\n";
      }
      else {
        &DEBUG_PRINT( "TOP DEBUG:" .$pattern."\n" , $outputtype);
        &UNWRAP_RECURSIVE(\*OUT, $pattern ,$subroutine_ref, 0, $outputtype);
      }
    }

    print OUT "end\nend\n";
    close(OUT);
  }
}

# ---------------------------
sub UNWRAP_TO_MULTI_WGL {
# ---------------------------
  my $pattern_ref     = shift;
  my %pattern_hash    = %$pattern_ref;

  my $subroutine_ref  = shift;
  my %subroutine_hash = %$subroutine_ref;

  my $timeplate_ref   = shift;
  my $signals_ref     = shift;

  my $outputtype      = shift;

  foreach my $pattern (keys %pattern_hash) {
    my $file = &EXTRACT_FN($pattern);

    &INFO_PRINT("Creating pattern for ".$file."\n", $outputtype);

    open(OUT, ">flat_$file.wgl") || die("ERROR: cannot open file \"flat_".$file.".wgl\" for writing !\n");
    &PRINT_HEADER(\*OUT, $file, $timeplate_ref, $signals_ref);

    print OUT "  pattern ".$pattern."\n";

    foreach my $pattern ( @{$$pattern_ref{$pattern}} ) {
      if ( $pattern =~ m/^\s*vector/ ) {
        print OUT $pattern."\n";
      }
      else {
        &DEBUG_PRINT( "TOP DEBUG:" .$pattern."\n" , $outputtype);
        &UNWRAP_RECURSIVE(\*OUT, $pattern ,$subroutine_ref, 0, $outputtype);
      }
    }

    print OUT "  end\n";
    print OUT "end\n";
    close(OUT);
  }
}

# ---------------------------
sub UNWRAP_TO_SINGLE_WGL {
# ---------------------------
  my $pattern_ref     = shift;
  my %pattern_hash    = %$pattern_ref;

  my $subroutine_ref  = shift;
  my %subroutine_hash = %$subroutine_ref;

  my $timeplate_ref   = shift;
  my $signals_ref     = shift;

  my $outputtype      = shift;

  open(OUT, ">flat_$filename") || die("ERROR: cannot open file \"flat_$filename\" for writing !\n");
  &PRINT_HEADER(\*OUT, $waveform_name, $timeplate_ref, $signals_ref);

  foreach my $pattern (keys %pattern_hash) {
    &INFO_PRINT("Creating pattern for ".&EXTRACT_FN($pattern)."\n", $outputtype);

    print OUT "  pattern ".$pattern."\n";

    $vector_nr = 0;
    foreach my $pattern ( @{$$pattern_ref{$pattern}} ) {
      if ( $pattern =~ m/^\s*vector/ ) {
        if ($vector_nr % 10 == 0) {
          print OUT $pattern."  {".$vector_nr."}\n";
        } else {
          print OUT $pattern."\n";
        }
        $vector_nr += 1;
      }
      else {
        &DEBUG_PRINT( "TOP DEBUG:" .$pattern."\n" , $outputtype);
        &UNWRAP_RECURSIVE(\*OUT, $pattern ,$subroutine_ref, 0, $outputtype);
      }
    }

    print OUT "  end\n";
  }

  print OUT "end\n";
  close(OUT);
}

# ---------------------------
sub UNWRAP_RECURSIVE {
# ---------------------------
  my $fh      = shift;
  my $call    = shift;
  my $sr_ref  = shift;
  my $depth   = shift;
  my $out_typ = shift;

  $depth++;

  if (! exists $$sr_ref{$call} ) {
    &INFO_PRINT( "WARN : Subroutine \"".$call."\" is undefined! Pattern will be incomplete!\n", $out_typ);
    return 0;
  }

  foreach my $vector ( @{$$sr_ref{$call}} ) {
    if ( $vector =~ m/^\s*\{/ ) {
      print $fh $vector."\n";
    } else {
      if ( $vector =~ m/^\s*vector/ ) {
        if ($vector_nr % 10 == 0) {
          print $fh $vector."  {".$vector_nr."}\n";
        } else {
          print $fh $vector."\n";
        }
        $vector_nr += 1;
      }
      else {
        &DEBUG_PRINT( &RECURSIVE_DEPTH($depth) . $vector . "\n", $out_typ);
        &UNWRAP_RECURSIVE($fh, $vector, $sr_ref, $depth, $out_typ);
      }
    }
  }

  if (($call !~ m/^jtag_cycle/) &&
      ($call !~ m/^jtag_incr_cycle/) &&
      ($call !~ m/^jtag_w1us_cycle/) &&
      ($call !~ m/^jtag_w1ms_cycle/)) {
    print OUT "    {subroutine exit}\n";
  }
}

# ---------------------------
sub PRINT_HEADER {
  my $fh      = shift;
  my $wf_name = shift;  # waveform name
  my $tp_ref  = shift;
  my $sig_ref = shift;

  print $fh "waveform ".$wf_name."\n";

  print $fh "  signal\n";
  foreach my $signal (@$sig_ref) {
    print $fh $signal."\n";
  }
  print $fh "  end\n";

  foreach my $timing (@$tp_ref) {
    print $fh $timing."\n";
  }
}
# ---------------------------

# ---------------------------
sub EXTRACT_FN {
# ---------------------------
  my $line = shift;

  my @arr=split(/\(/, $line);

  return $arr[0];
}

# ---------------------------
sub RECURSIVE_DEPTH {
# ---------------------------
  my $depth = shift;

  my $INDENT_SIGN = "  ";
  my $indent = "";

  for my $i (0..$depth) {
    $indent=$indent.$INDENT_SIGN;
  }

  return $indent;
}

# ---------------------------
sub INFO_PRINT {
# ---------------------------
  my $string = shift;
  my $typ    = shift;

  print STDOUT $string;
}

# ---------------------------
sub DEBUG_PRINT {
# ---------------------------
  my $string = shift;
  my $typ    = shift;

  if ( $typ == 1 ) {
    print STDERR $string;
  }
  elsif ( $typ == 2 ) {
    print STDERR colored( $string, 'bold blue');
  }
}

