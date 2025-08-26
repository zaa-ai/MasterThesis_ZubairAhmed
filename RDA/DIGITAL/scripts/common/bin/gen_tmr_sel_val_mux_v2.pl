#!/usr/bin/perl -w

#############################################################################
# Author        : Alexander Sonntag, MAZ Brandenburg GmbH
#                 Josef Polak, MAZ Brandenburg GmbH
#
# Description   : sel val parser
#
# Category      : Design Flow
# Project       : DFLOW
#############################################################################
# Modified      : 2011-02-02 AS Initial version
#############################################################################

use strict;


if (@ARGV > 4) {die "Check Number of Command Line Parameters.\n"};


my $filename    = shift;      # sel val interface
my $includefile = shift;      # generated include file
my $includefile3= shift;      # generated include for tb

my $line;
my @inputlist;
my @outputlist;
my @inoutlist;

my @entitylist;
my @analog_parameter_list;
my $parameters_found = 0;
my $outputs;
my $inputs;
my $inouts;

my $module_name;

my @define; push @define,"";

# TEST_MUX parser
my $vlog_entity_passed = 0;
my $vlog_module_name;
my @all_ports_list;
my @muxed_list;
my @parameter_list;

my $tmr_sel_cnt = 0;
my $tmr_val_cnt = 0;
my $tmr_one_cnt = 0;

my $tmr_sel_msb = 0;
my $tmr_val_msb = 0;
my $tmr_one_msb = 0;

my $width_msb;


# PAD IN TEST_MUX parser
my $pad_in_vlog_module_name;
my @pad_in_all_ports_list;
my @pad_in_muxed_list;
my @pad_in_parameter_list;

# TMR ONE MUX parser
my $tmr_one_vlog_module_name;
my @tmr_one_all_ports_list;
my @tmr_one_muxed_list;
my @tmr_one_parameter_list;

# AMS related signals
my @ams_related_list;

# ---------------------------------------------------------------
# generate new shell
# ---------------------------------------------------------------

  &PARSE_INTERFACE;
  &ADD_ENTITY;
  &ADD_TMR_MASK;    #requires ->&ADD_ENTITY
  &ADD_FOOTER;

# ---------------------------------------------------------------
# Subroutines
# ---------------------------------------------------------------



# -------------
sub PARSE_INTERFACE{
# -------------

  # ---------------------------------------------------------------
  #open filename
  # ---------------------------------------------------------------
  if ($filename eq "") {die "$filename not found\n"}
  else{
      open(IN, "<$filename") || die("ERROR: cannot open file \"$filename\" for read !\n");
  }

my  $in_entity = 0;
my  $entity_passed = 0;
  # ---------------------------------------------------------------
  #parse INTERFACE file
  # ---------------------------------------------------------------
  while(<IN>){

    $line=$_;             #get line
    $line=~ s/  / /g;         #substitute tab by space

    if ($entity_passed == 0) {
      if ($line=~ m/^\s*interface\s*(\w+)\s*;/){
        $in_entity   = 1;
        $module_name = $1;
      }

      if ($in_entity){

        # get input signals
        if ($line=~ m/^\s*wire\s*(\[\S+\])\s*(\w+)/){  # grep input signals width and name
          $inputs = {
              WIDTH      => $1,
              NAME       => $2,
              TMR_SEL_VAL=> 0,
            DEFINE     => $define[-1],
          };
          if ($line=~ m/TMR_SEL_VAL/){               # grep input signals width and name
            $inputs->{TMR_SEL_VAL} = 1;
            push @inputlist,$inputs;
            $inputs->{DIR} = "D2A";
            if ($line=~ m/TMR_SEL_VAL\s+A2D/){
              $inputs->{DIR} = "A2D";
            }
          }
        }
        else {
          if ($line=~ m/^\s*wire\s*(\w+)/) {           # grep input signals name only
            $inputs = {
                WIDTH      => "",
                NAME       => $1,
                TMR_SEL_VAL=> 0,
              DEFINE     => $define[-1],
            };
            if ($line=~ m/TMR_SEL_VAL/){               # grep input signals width and name
              $inputs->{TMR_SEL_VAL} = 1;
              push @inputlist,$inputs;
              $inputs->{DIR} = "D2A";
              if ($line=~ m/TMR_SEL_VAL\s+A2D/){
                $inputs->{DIR} = "A2D";
              }
            }
          }
        }
      } #in_entity


      if ($line=~ m/endinterface/){
            $entity_passed = 1;
            $in_entity     = 0;
      }
    }
  }
  close (IN);
}


# -------------
sub ADD_ENTITY{
# -------------
  print "// ---------------------------------------------\n";
  print "// AUTOMATICALLY GENERATED FILE -> DO NOT CHANGE\n";
  print "// --> use gen_tmr_sel_val_mux.pl <interface_file> <include file> > tmr_sel_val_mux.v\n";
  print "// ---------------------------------------------\n";
  print "\n";
  print "`timescale 1ns/1ns\n\n";
  print "`include \"tmr_inc.v\"\n\n";

  print "module tmr_sel_val_mux #(\n";        # create new module
  print "    parameter DOMAIN_3V0 = 0\n";
  print "  )(\n";
  foreach my $listitem(@inputlist){
    if ($listitem->{TMR_SEL_VAL}){
      my $width = $listitem->{WIDTH};
      while (length($width) < 6) {
        $width = " " . $width;
      }
      if ($listitem->{DIR} eq "A2D") {
        print "    input  $width $listitem->{NAME},\n";
      } else {
        print "    output $width $listitem->{NAME},\n";
      }
    }
  }
  print "\n";
  print "    input  [`NUM_SEL_TMRS-1:0] tmr_sel,\n";
  print "    input  [`NUM_VAL_TMRS-1:0] tmr_val,\n";
  print "\n";
  print "    $module_name.mp io\n";
  print "  );\n\n";

  print "  `include \"tmr_sel_val_inc.v\"\n\n";

  print "  // pure muxes\n";                       # add non-muxed test_mux ports to entity

  print "\n";
}




# -------------
sub ADD_TMR_MASK{
# -------------
  # This requires previous execution of sub ADD_ENTITY!!!

  #open filename
  if ($includefile eq "") {die "$includefile not found\n"}
  else{
      open(INC, ">$includefile") || die("ERROR: cannot open file \"$includefile\" for write !\n");
  }

  if ($includefile3 eq "") {}
  else{
      open(INC3, ">$includefile3") || die("ERROR: cannot open file \"$includefile3\" for write !\n");
  }

  #calculate sel val msbs
   foreach my $listitem(@inputlist){
       if ($listitem->{TMR_SEL_VAL}){
         $width_msb = 0;
         $tmr_sel_cnt++;
         if ($listitem->{WIDTH}=~ m/\[(\w+):/){  #grep msb
           $width_msb = $1;
         }
         $tmr_val_cnt = $tmr_val_cnt + $width_msb + 1;
       }
   }

   $tmr_sel_msb = $tmr_sel_cnt-1;
   $tmr_val_msb = $tmr_val_cnt-1;


  print INC "\n// TMR_MUX BITS INCLUDE FILE --> Automatically generated by gen_tmr_sel_val_mux.pl -DO NOT CHANGE- <--\n\n";
  print INC "`define TMR_MUX_VAL_MSB $tmr_val_msb\n";
  print INC "`define TMR_MUX_SEL_MSB $tmr_sel_msb\n";
  print INC "\n";

  unless ($includefile3 eq ""){
  print INC3"\n// TMR_MUX TB INCLUDE FILE --> Automatically generated by gen_tmr_sel_val_mux.pl -DO NOT CHANGE- <--\n\n";
  print INC3"\n";
  print INC3"\n// generate testbench tasks\n";
  print INC3"\n";
  }
  $tmr_sel_cnt = 0;
  $tmr_val_cnt = 0;



  foreach my $listitem(@inputlist){
    if ($listitem->{TMR_SEL_VAL}){
      $width_msb = 0;
      if ($listitem->{WIDTH}=~ m/\[(\w+):/){
        $width_msb = $1;
      }
      my $upper_bit = $tmr_val_cnt + $width_msb;
      print "  pure_mux #(.DOMAIN_3V0(DOMAIN_3V0)) pure_mux_$listitem->{NAME}\_inst $listitem->{WIDTH} (\n";
      print "    .i_a (tmr_val[`B_TMR_MUX_VAL_\U$listitem->{NAME}]),\n";
      if ($listitem->{DIR} =~ m/A2D/) {
        print "    .i_b ($listitem->{NAME}),\n";
        print "    .i_sa(tmr_sel[`B_TMR_MUX_SEL_\U$listitem->{NAME}]),\n";
        print "    .o_y (io.$listitem->{NAME})\n";
      } else {
        print "    .i_b (io.$listitem->{NAME}),\n";
        print "    .i_sa(tmr_sel[`B_TMR_MUX_SEL_\U$listitem->{NAME}]),\n";
        print "    .o_y ($listitem->{NAME})\n";
      }
      print "  );\n";
      print "\n";

      #output to include
      print INC "`define B_TMR_MUX_VAL_\U$listitem->{NAME} $upper_bit:$tmr_val_cnt\n";
      print INC "`define B_TMR_MUX_SEL_\U$listitem->{NAME} $tmr_sel_cnt\n\n";

      unless ($includefile3 eq ""){
      print INC3"  task   SET_TMR_SEL_VAL_\U$listitem->{NAME}\E; input $listitem->{WIDTH} val; begin tmr_sel_vector\[\`B_TMR_MUX_SEL_\U$listitem->{NAME}\E\]  = 1'b1; tmr_val_vector[`B_TMR_MUX_VAL_\U$listitem->{NAME}\E\] = val; SET_TMR_SEL_VAL; end endtask\n";
      if ($listitem->{DIR} =~ m/A2D/) {
        print INC3"  task CHECK_TMR_SEL_VAL_\U$listitem->{NAME}\E; input $listitem->{WIDTH} exp; begin compare(`DIGITAL_INST.tmr_sel_val_io.$listitem->{NAME}   , exp, \"\U$listitem->{NAME}\E\"); end endtask\n\n";
      } else {
        print INC3"  task CHECK_TMR_SEL_VAL_\U$listitem->{NAME}\E; input $listitem->{WIDTH} exp; begin compare(`DIGITAL_INST.$listitem->{NAME}   , exp, \"\U$listitem->{NAME}\E\"); end endtask\n\n";
      }
      }

      $tmr_sel_cnt++;
      $tmr_val_cnt = $tmr_val_cnt + $width_msb + 1;
    }
  }

  close (INC);
  close (INC3);

}

# -------------
sub TMR_MUX_CHECKER{
# -------------

  #instance of test_mux


  foreach my $listitem(@inputlist){
    if ($listitem->{TMRMUX}){
      if (!&NAME_IN_LIST($listitem->{NAME}, @all_ports_list) ){
        print "    WARNING: please add $listitem->{NAME} to TEST_MUX table!   // TODO\n";   #item not found in test_mux
      }
    }
  }
}



# -------------
sub ADD_FOOTER{
# -------------

  print "endmodule\n\n";

  #&TMR_MUX_CHECKER;
}


# -------------
sub NAME_IN_LIST{
# -------------
  my($name,@list) = @_;  # parameters
  my $found = 0;

  foreach my $listitem(@list){
    if ($listitem->{NAME} eq $name) {$found++;}
  }
  return $found;
}

# -------------
sub STRING_IN_LIST{
# -------------
  my($str,@list) = @_;  # parameters
  my $found = 0;

  foreach my $listitem(@list){
    if ($listitem eq $str) {$found++;}
  }
  return $found;
}
