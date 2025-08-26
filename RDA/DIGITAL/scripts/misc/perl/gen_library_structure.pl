#!/usr/bin/perl
##########################################################################
# 1. Download Memory Compiler from here:
# http://intranet.elmos.de/leitstand/design/groups/standardisierung/html/index.php?tech=AMSTERDAM
#
# 2. Extract archive in your Path
#
# 3. Navigate to the path where the compiler script is located as link:
# e.g. <yourPath>bcd1370_memory_compiler_vrom_hd_BE-Common_sec190806_0043/MemoryCompiler_BE/vrom_hd/FB-V1.00 for ROM Compiler
#
# 4. Adapt the needed files (path_file, batchfile)
#
# 5. Run compiler with adapted files
#
# 6. Navigate to or copy the results to one folder
#
# Optional: Link this script in to the folder with the results
# 			Adapt the path to the techfile in this script
#			Run script and if you have luck all is fine afterwards :)
############################################################################

use strict;
use warnings;

use lib '/common/department/design/tools/designflow/develop/perl/lib';

use File::Path qw(make_path remove_tree);
use File::Copy::Recursive qw(fcopy rcopy dircopy fmove rmove dirmove);
use File::Basename;
use Cwd;

use Shell;
use Modulecmd;

#############################################################################
# Setup
#############################################################################
# The only thing that must be provided is the path to the techfile for
# Milkyway data generation
make_path("tech");
fcopy("../../../tech/BCD1370_10t_5LM.tf", "tech/BCD1370_10t_5LM.tf" );

my $techfile = cwd()."/tech/BCD1370_10t_5LM.tf";

open(FILE,$techfile)
or die "Kann $techfile nicht lesen: $!\n This file is necessary for Milkyway data generation!\n";
close(FILE);

#############################################################################
# Loading module for Library Compiler
#############################################################################
my $lc_version = undef;
load_lc_version($lc_version) unless Modulecmd::is_loaded("lc");

sub load_lc_version {
	my ($version) = @_;
	$version = "L-2016.06-SP1"
	  unless defined $version;    #Version lc/O-2018.06-SP2 doesnt work properly
	Modulecmd::load_module( "lc", $version )
	  unless Modulecmd::is_loaded( "lc", $version );
	$lc_version = $version;
}

#############################################################################
# Loading module for Milkywas Compiler
#############################################################################
my $mw_version = undef;
load_mw_version($mw_version) unless Modulecmd::is_loaded("milkyway");

sub load_mw_version {
	my ($version) = @_;
	$version = "O-2018.06-SP2" unless defined $version;
	Modulecmd::load_module( "milkyway", $version )
	  unless Modulecmd::is_loaded( "milkyway", $version );
	$mw_version = $version;
}

#############################################################################
# Getting Instance name (extracted from lef-file
#############################################################################

our $instName = undef;
opendir( DIR, "./" ) || die "can't read current dir\n";
foreach ( grep( /^.*\.lef$/, readdir DIR ) ) {
	( $instName = $_ ) =~ s/.lef//;
}
close DIR;
print "Processing steps for Instance $instName \n";

#############################################################################
# Create folder structure
#############################################################################

my @folders = (
	"cd", "db",      "doc",  "gds", "liberty", "models",
	"mw", "netlist", "tech", "tetramax"
);

foreach my $f (@folders) {
	if ( $f && !-d $f ) {
		make_path("$f");
	}
}

######################################################
# Change Bus delimeter in cdl-Netlist from [] to <>
# and copy changed cdl netlist to folder ./netlist
######################################################
my @lines          = ();
my @newlines       = ();
my $patch_netlist = 1;

if ( $patch_netlist == 0 ) {
# Just copy it without patching because of LVS problems with compiler version 1.02
	my @cdlfile = glob("*.cdl");

	for my $file (@cdlfile) {
		fcopy( $file, "netlist" ) or die "Copy failed: $!";
	}
	chdir "./netlist";
}
else {	# Or set $patch_netlist to 1 to replace brackets
	#read in original file
	open( FILE, "<$instName.cdl" ) || die "File $instName.cdl not found";
	@lines = <FILE>;
	close(FILE);

	chdir "./netlist";

	# Do replacement of bus delimineters -> not neccessary?
	# Some devices are instatiated without X in Front e.g.
	# .subckt bcd1370_mc_vromp_hd_8192x32m16_14 D G S B TW VSX VDDE VSSE
	# MN0 D G S B TW VSX tw_lvn m=1 w=NW l=NL nf=NFN
	# .ends bcd1370_mc_vromp_hd_8192x32m16_14
	# So we put a X in Front of it to not run in LVS problems
	@newlines = ();
	foreach (@lines) {
		$_ =~ s/^M/XM/g;
	    $_ =~ s/^D/XD/g;
		#$_ =~ s/\[/\</g;
		#$_ =~ s/\]/\>/g;
		push( @newlines, $_ );
	}

	#write out in new file in folder ./netlist
	open( FILE, ">$instName.cdl" ) || die "File $instName.cdl not found";
	print FILE @newlines;
	close(FILE);
}

print "Finished patching/copying CDL netlist \n";

######################################################
# Adding Pininfo to cdl-netlist and copy it to *.lvs.cdl
######################################################
# read in patched/copied netlist
@lines = ();
open( FH, "$instName.cdl" ) || die "File $instName.cdl not found!";
@lines = <FH>;
close FH;

#
# add PININFO information to .cdl
#
my $fi   = 0;
my $pins = undef;
my @pins = undef;
my $l    = undef;
my $p    = undef;
my $i    = undef;
open( OUT, ">$instName.lvs.cdl" ) || die "File $instName.lvs.cdl not found";

foreach $l (@lines) {

   #	if ( ( $fi == 0 ) && ( $l =~ m/\.subckt $instName (.*)/ ) )
   #	{    # Suche nach Topinstanz
   #		$pins .= $1;
   #		$fi = 1;
   #	}
   #	elsif ( ( $fi == 1 ) && ( $l =~ m/\+(.*)/ ) )
   #	{    # Suche nach nachfolgenden Zeilen die + und beliebige Zeichn enthalten
   #		$pins .= $1;
   #	}
   #	elsif ( ( $fi == 1 ) && ( $l !~ m/\+(.*)/ ) )
   #	{    # Suche nach der Zeile die kein + mehr am Anfang enthält
   #		$fi = 0;
   #		print OUT "*.PININFO ";
   #		@pins = split( ' ', $pins );
   #		$i = 1;
   #		foreach $p (@pins) {
   #			if ( !( $i % 8 ) ) {
   #				print OUT "\n*.PININFO ";
   #			}    # $i % x legt fest wie viele pins auf einer Zeile stehen
   #			if ( $p =~ m/DOUT/ ) {
   #				print OUT " $p:O";
   #			}
   #			elsif ( $p =~ m/VDDE|VSX|VSSE/ ) {
   #				print OUT " $p:B";
   #			}
   #			else {
   #				print OUT " $p:I";
   #			}
   #			$i++;
   #		}
   #
   #		print OUT "\n";
   #	}
	print OUT $l;
}
close OUT;
print "Added Pininfo to $instName.lvs.cdl \n";

######################################################
# Comment .PARAM section and replacing parameters with its values 
######################################################
my @params;
my @values;
$l = undef;
#push parameter/value pairs in to arrays (ToDo: Try it with a hash)
foreach $l (@lines) {
	if ( $l =~ m/\.PARAM (\w+) = ([\d.]+u)/ ) {
		push @params, $1;
		push @values, $2;
	}
}

# Clear @newlines
@newlines = ();

# Comment the .PARAM section and write it to @newlines
foreach (@lines) {
	$_ =~ s/\.PARAM/*.PARAM /g;
	push( @newlines, $_ );
}
#write out @newline in new file
open( FILE, ">$instName.lvs.cdl.upd" )
  || die "File $instName.lvs.cdl.upd not found";
print FILE @newlines;
close(FILE);

print "Commented .PARAM section in file $instName.lvs.cdl.upd. \n";

for ( my $f = eval( @params - 1 ) ; $f >= 0 ; $f = $f - 1 ) {

	my $param = $params[$f];
	my $value = $values[$f];

	# read in patched netlist
	@lines = ();
	open( FH, "$instName.lvs.cdl.upd" )
	  || die "File $instName.lvs.cdl.upd not found!";
	@lines = <FH>;
	close FH;

	unlink "$instName.lvs.cdl.upd";    #delete old file

	open( OUT, ">$instName.lvs.cdl.upd" ) or die $!;    # open new file

	print "f = $f, param = $param, value = $value \n";
	foreach my $line (@lines) {
		$line =~ s/$param/$value/g if defined $param && defined $value;
		print OUT $line;
	}
	close(OUT) or die $!;
}
unlink "$instName.lvs.cdl";
rename("$instName.lvs.cdl.upd","$instName.lvs.cdl");

chdir "../";

print "Finished creating CDL netlist for LVS.\n";

######################################################
# Generate db-files and copy folder db
######################################################
# db processing
opendir( DIR, "./" ) || die "can't read current dir\n";
foreach ( grep( /^.*\.lib$/, readdir DIR ) ) {
	( my $dotlibfile = $_ ) =~ s/.lib//;
	open( SH, ">$dotlibfile.sh" )
	  or die "can't open file $dotlibfile.sh to write\n";
	print SH "read_lib $dotlibfile.lib\n";
	print SH "write_lib -format db $dotlibfile -output $dotlibfile.db\n";
	print SH "exit\n";
	close SH;
	system("lc_shell -f $dotlibfile.sh");
	system("rm $dotlibfile.sh");
	fcopy( "$dotlibfile.db", "db" );
}
close DIR;

######################################################
# Generate Milkyway data
######################################################
# mw processing
opendir( DIR, "./" ) || die "can't read current dir\n";
our $leffile = undef;
foreach ( grep( /^.*\.lef$/, readdir DIR ) ) {
	( $leffile = $_ ) =~ s/.lef//;
	print $leffile;
	fcopy( "$leffile.lef", "mw" );
}
close DIR;

chdir "./mw/";
open( CMD, ">$leffile.cmd" ) or die "can't open file $leffile.cmd to write\n";
print CMD "(tcl \"extend_mw_layers\")\n";
print CMD ";# Scheme\n";
print CMD "cmCreateLib\n";
print CMD "setFormField \"Create Library\" \"Set Case Sensitive\" \"1\"\n";
print CMD "setFormField \"Create Library\" \"Library Name\" \"$leffile\_LIB\"\n";
print CMD "setFormField \"Create Library\" \"Technology File Name\" \"$techfile\"\n";
print CMD "formOK \"Create Library\"\n";
print CMD "geOpenLib\n";
print CMD "setFormField \"Open Library\" \"Library Name\" \"$leffile\_LIB\"\n";
print CMD "formOK \"Open Library\"\n";
print CMD "read_lef\n";
print CMD "setFormField \"Read LEF\" \"Library Name\" \"$leffile\_LIB\"\n";
print CMD "setFormField \"Read LEF\" \"Cell LEF Files\" \"./$leffile.lef\"\n";
print CMD "formOK \"Read LEF\"\n";
print CMD "(dbSaveCell (geGetEditCell))\n";
print CMD "geConfirmCloseLib\n";
print CMD "formYes \"Dialog Box\"\n";
print CMD "menuQuit\n";
print CMD "formYes \"Dialog Box\"\n";
close CMD;
system("Milkyway -replay $leffile.cmd -nogui");

chdir "../";
######################################################
# Generating cdesigner database
######################################################

# 1. change current working direcrory to cd
chdir "./cd";

# 2. Create work area for cdesigner
system("/common/run/synopsys/pdk/amsterdam/latest/bin/mksnpsproject");

# Creating folder synopsys_custom and prefs.xml for cdesigner -> not necessary because no schematic creation?

system("mkdir synopsys_custom");
open (FH, ">synopsys_custom/prefs.xml");
print FH "<?xml version=\"1.0\"?>";
print FH "<!-- created by Custom Compiler build#  ,on -->";
print FH "<file-format version=\"1.0\" name=\"synopsysPrefs\">";
print FH "        <preferences>";
print FH "                <pref value=\"true\" name=\"dbSchGenMergeSubports\"/>";
print FH "        </preferences>";
print FH "</file-format>";

#
# creating tcl file for cdesigner
#
open (FH, ">createCD.tcl");
### ToDo: All following commands should also work without gui
# dm::createLib <name: string> -path <string> [-dmSystem <string>] [-assign <string>] [-attrs [<map>]]

#print FH "dm::createLib $instName .\n";
### Uncomment if you want custom compiler with gui
#
# New library with name=$instName
#
print FH "dm::showNewLibrary\n";
print FH "gi::setField {libName} -value $instName -in [gi::getDialogs {dmNewLibrary}]\n";
print FH "gi::pressButton {/ok} -in [gi::getDialogs {dmNewLibrary}]\n";
#
# import gds file
#
print FH "db::showImportStream\n";
print FH "gi::setField {fileName} -value \"../$instName.gds\" -in [gi::getDialogs {dbImportStream}]\n";
print FH "gi::setField {libName} -value $instName -in [gi::getDialogs {dbImportStream}]\n";
print FH "gi::pressButton {ok} -in [gi::getDialogs {dbImportStream}]\n";
print FH "db::foreach xtJob [xt::getJobs importStream*] {\n  xt::wait \$xtJob\n}\n";
print FH "de::sendMessage \"GDS is imported!\"\n";
#
# import cdl netlist
#
print FH "db::showImportText\n";
print FH "gi::setField {language} -value {CDL} -in [gi::getDialogs {dbImportText}]\n";
print FH "gi::setField {libName} -value $instName -in [gi::getDialogs {dbImportText}]\n";
print FH "gi::setField {fileName} -value {../netlist/$instName.lvs.cdl} -in [gi::getDialogs {dbImportText}]\n";
#print FH "gi::setField {deviceMapFile} -value {../sources/$map} -in [gi::getDialogs {dbImportText}]\n";#derzeit kein instance map file vorhanden
print FH "gi::setField {overwriteDesigns} -value {Always} -in [gi::getDialogs {dbImportText}]\n";
print FH "gi::setField {generateSymbols} -value {true} -in [gi::getDialogs {dbImportText}]\n";
print FH "gi::setField {overwriteSymbols} -value {Always} -in [gi::getDialogs {dbImportText}]\n";
print FH "gi::setField {generateSchematics} -value {false} -in [gi::getDialogs {dbImportText}]\n";#false da keine instance map file 
print FH "gi::setField {topModule} -value {} -in [gi::getDialogs {dbImportText}]\n";
print FH "gi::pressButton {ok} -in [gi::getDialogs {dbImportText}]\n";
print FH "de::sendMessage \"CDL is imported!\"\n";
#
# import verilog netlist top module and overwrite created symbol
#
print FH "db::showImportText\n";
print FH "gi::setField {language} -value {Verilog} -in [gi::getDialogs {dbImportText}]\n";
print FH "gi::setField {libName} -value $instName -in [gi::getDialogs {dbImportText}]\n";
print FH "gi::setField {fileName} -value {../$instName.v} -in [gi::getDialogs {dbImportText}]\n";
#print FH "gi::setField {deviceMapFile} -value {../sources/$map} -in [gi::getDialogs {dbImportText}]\n";#derzeit kein instance map file vorhanden
print FH "gi::setField {overwriteDesigns} -value {Never} -in [gi::getDialogs {dbImportText}]\n";
print FH "gi::setField {defines} -value {POWER_PINS} -in [gi::getDialogs {dbImportText}]\n";
print FH "gi::setField {generateSymbols} -value {true} -in [gi::getDialogs {dbImportText}]\n";
print FH "gi::setField {overwriteSymbols} -value {Always} -in [gi::getDialogs {dbImportText}]\n";
print FH "gi::setField {generateSchematics} -value {false} -in [gi::getDialogs {dbImportText}]\n";#false da keine instance map file 
print FH "gi::setField {modules} -value {$instName} -in [gi::getDialogs {dbImportText}]\n";
print FH "gi::pressButton {ok} -in [gi::getDialogs {dbImportText}]\n";
print FH "de::sendMessage \"Verilog is imported!\"\n";
#
# do DRC
# ToDo: specify $rsDRCFileICV
#print FH "set context [de::open [dm::getCellViews layout -libName $instName -cellName $instName]]\n";
#print FH "set num [db::getAttr window -of \$context]\n";
#print FH "xt::showDRCSetup -job drc -window \$num\n";
#print FH "gi::setField {/tabGroup/mainTab/jobParametersGroup/runsetFile/entryField} -value {$rsDRCFileICV} -in [gi::getDialogs {xtDRCSetup} -parent \$num]\n";
#print FH "gi::setField {/tabGroup/mainTab/jobParametersGroup/launchDebugger} -value {false} -in [gi::getDialogs {xtDRCSetup} -parent \$num]\n";
#print FH "gi::setField {/tabGroup/mainTab/jobParametersGroup/viewOutput} -value {false} -in [gi::getDialogs {xtDRCSetup} -parent \$num]\n";
#print FH "gi::pressButton {/ok} -in [gi::getDialogs {xtDRCSetup} -parent \$num]\n";
#print FH "de::close \$context\n";
#print FH "db::foreach xtJob [xt::getJobs icv_drc*] {\n  xt::wait \$xtJob\n}\n";
#print FH "de::sendMessage \"DRC is finished!\"\n";

#
# do LVS
# ToDo: specify $rsLVS file
#print FH "set context [de::open [dm::getCellViews layout -libName $instName -cellName $instName]]\n";
#print FH "set num [db::getAttr window -of \$context]\n";
#print FH "xt::showLVSSetup -job lvs -window \$num\n";
#print FH "gi::setField {/tabGroup/mainTab/schematicGroup/schematicFormat/netlist} -value {true} -in [gi::getDialogs {xtLVSSetup} -parent \$num]\n";
#print FH "gi::setField {/tabGroup/mainTab/schematicGroup/schematicInputNetlistFormat} -value {CDL} -in [gi::getDialogs {xtLVSSetup} -parent \$num]\n";
#print FH "gi::setField {/tabGroup/mainTab/schematicGroup/schematicInputNetlist/entryField} -value {../netlist/$instName.lvs.cdl} -in [gi::getDialogs {xtLVSSetup} -parent \$num]\n";
#print FH "gi::setField {/tabGroup/mainTab/schematicGroup/schematicCellName} -value {$instName} -in [gi::getDialogs {xtLVSSetup} -parent \$num]\n";
#print FH "gi::setField {/tabGroup/mainTab/jobParametersGroup/launchDebugger} -value {false} -in [gi::getDialogs {xtLVSSetup} -parent \$num]\n";
#print FH "gi::setField {/tabGroup/mainTab/jobParametersGroup/viewOutput} -value {false} -in [gi::getDialogs {xtLVSSetup} -parent \$num]\n";
#print FH "gi::setField {/tabGroup/mainTab/jobParametersGroup/runsetFile/entryField} -value $rsLVS -in [gi::getDialogs {xtLVSSetup} -parent \$num]\n";
#print FH "gi::setField {/tabGroup/mainTab/jobParametersGroup/toolOptions} -value {} -in [gi::getDialogs {xtLVSSetup} -parent \$num]\n";
#print FH "gi::pressButton {/ok} -in [gi::getDialogs {xtLVSSetup} -parent \$num]\n";
#print FH "de::close \$context\n";
#print FH "db::foreach xtJob [xt::getJobs *_lvs*] {\n  xt::wait \$xtJob\n}\n";
#print FH "de::sendMessage \"LVS is finished!\"\n";

#
# #do LPE
#
#
# #LVS for LPE
#print FH "set context [de::open [dm::getCellViews layout -libName $instName -cellName $instName]]\n";
#print FH "set num [db::getAttr window -of \$context]\n";
#print FH "xt::showLVSSetup -job lvs -window \$num\n";
#
#print FH "gi::setField {/tabGroup/mainTab/schematicGroup/schematicFormat/netlist} -value {true} -in [gi::getDialogs {xtLVSSetup} -parent \$num]\n";
#print FH "gi::setField {/tabGroup/mainTab/schematicGroup/schematicInputNetlistFormat} -value {CDL} -in [gi::getDialogs {xtLVSSetup} -parent \$num]\n";
#print FH "gi::setField {/tabGroup/mainTab/schematicGroup/schematicInputNetlist/entryField} -value {../results/$instName.cdl} -in [gi::getDialogs {xtLVSSetup} -parent \$num]\n";
#print FH "gi::setField {/tabGroup/mainTab/jobParametersGroup/launchDebugger} -value {false} -in [gi::getDialogs {xtLVSSetup} -parent \$num]\n";
#print FH "gi::setField {/tabGroup/mainTab/jobParametersGroup/viewOutput} -value {false} -in [gi::getDialogs {xtLVSSetup} -parent \$num]\n";
#print FH "gi::setField {/tabGroup/mainTab/jobParametersGroup/toolOptions} -value {} -in [gi::getDialogs {xtLVSSetup} -parent \$num]\n";
#print FH "gi::setField {/tabGroup/mainTab/jobParametersGroup/runsetFile/entryField} -value $rsLVS4LPE -in [gi::getDialogs {xtLVSSetup} -parent \$num]\n";
#print FH "gi::pressButton {/ok} -in [gi::getDialogs {xtLVSSetup} -parent \$num]\n";
#print FH "de::close \$context\n";
#print FH "db::foreach xtJob [xt::getJobs *_lvs*] {\n  xt::wait \$xtJob\n}\n";
#print FH "de::sendMessage \"LVS for LPE is finished!\"\n";

# #LPE
# #To Do
#print FH "set context [de::open [dm::getCellViews layout -libName $instName -cellName $instName]]\n";
#print FH "set num [db::getAttr window -of \$context]\n";
#
#print FH "xt::showLPESetup -job lpe -window \$num\n";
#print FH "gi::setField {/tabGroup/mainTab/jobParametersGroup/runsetFile/entryField} -value $rsLPE -in [gi::getDialogs {xtLPESetup} -parent \$num]\n";
##print FH "gi::setField {/tabGroup/extractionOptionsTab/layoutExtractionGroup/milkywayDatabase/entryField} -value $mwOutput -in [gi::getDialogs {xtLPESetup} -parent \$num]\n";
#print FH "gi::setField {/tabGroup/extractionOptionsTab/extraction} -value {C} -in [gi::getDialogs {xtLPESetup} -parent \$num]\n";
#print FH "gi::setField {/tabGroup/extractionOptionsTab/reduction} -value {NO} -in [gi::getDialogs {xtLPESetup} -parent \$num]\n";
##print FH "gi::setField {/tabGroup/extractionOptionsTab/accuracyMode} -value {400} -in [gi::getDialogs {xtLPESetup} -parent \$num]\n";
#print FH "gi::setField {/tabGroup/extractionOptionsTab/layoutExtractionGroup/icvRunsetReportFile/entryField} -value $rsRepFile -in [gi::getDialogs {xtLPESetup} -parent \$num]\n";
#print FH "gi::setField {/tabGroup/outputOptionsTab/outputGroup/outputFormat} -value {SPF} -in [gi::getDialogs {xtLPESetup} -parent \$num]\n";
#print FH "gi::setField {/tabGroup/outputOptionsTab/outputGroup/outputRunset/entryField} -value $rsOutput -in [gi::getDialogs {xtLPESetup} -parent \$num]\n";
#print FH "gi::setField {/tabGroup/outputOptionsTab/outputGroup/netlistPortOrderSelector} -value {false} -in [gi::getDialogs {xtLPESetup} -parent \$num]\n";
#print FH "gi::setField {/tabGroup/outputOptionsTab/outputGroup/netlistFile/entryField} -value $nlSPF -in [gi::getDialogs {xtLPESetup} -parent \$num]\n";
#print FH "gi::pressButton {/ok} -in [gi::getDialogs {xtLPESetup} -parent \$num]\n";
#
#print FH "de::close \$context\n";
#
#print FH "db::foreach xtJob [xt::getJobs starrc_lpe*] {\n  xt::wait \$xtJob\n}\n";
#print FH "de::sendMessage \"LPE is finished!\"\n";

print FH "exit -force true\n";
close FH;

#
# Start cdesigner and source tcl file
#
system("cdesigner -tcl createCD.tcl");

#
# ToDo: Edit Symbol...
#

chdir "../";

######################################################
# Doc processing
######################################################
opendir( DIR, "./" ) || die "can't read current dir\n";
foreach ( grep( /^.*\.ps$/, readdir DIR ) ) {
	( my $documentationfiles = $_ ) =~ s/.ps//;
	system("ps2pdf $_ $documentationfiles.pdf");
	fcopy( "$documentationfiles.pdf", "doc" );
}

# ASCII documentation
my @docfiles = glob("*.dat");

for my $file (@docfiles) {
	fcopy( $file, "doc" ) or die "Copy failed: $!";
}

close DIR;

######################################################
# gds processing
######################################################
my @gdsfiles = glob("*.gds");

for my $file (@gdsfiles) {
	fcopy( $file, "gds" ) or die "Copy failed: $!";
}

######################################################
# liberty processing
######################################################
my @libfiles = glob("*.lib");

for my $file (@libfiles) {
	fcopy( $file, "liberty" ) or die "Copy failed: $!";
}

######################################################
# models processing
######################################################
my @modelfiles = glob("*.v");

for my $file (@modelfiles) {
	fcopy( $file, "models" ) or die "Copy failed: $!";
}

#######################################################
## netlist processing
#######################################################
#my @cdlfiles = glob("*.cdl");
#
#for my $file (@cdlfiles) {
#	fcopy( $file, "netlist" ) or die "Copy failed: $!";
#}

######################################################
# tetramax model
######################################################
my @tmaxfiles = glob("*.tv");

for my $file (@tmaxfiles) {
	fcopy( $file, "tetramax" ) or die "Copy failed: $!";
}

# 5. cleanup not needed stuff and pack the rest in an archive

#system ("rm lc_output.txt lc_command.log *.info *.pl *.run *.env *.cc_init .vlstatus");
#chdir "./mw/";
#system ("rm *.cmd *.tcl Milkyway.*");
#chdir "../";
#system ("rm -r tech");

