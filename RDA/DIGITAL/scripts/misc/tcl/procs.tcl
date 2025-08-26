# #############################################################################
# Procedure to pause a script or sub-script. "cont" or "break" will continue the script.
# This is not very robust. Wrong commands will disturb the break loop.
# Alternative to return [-level n] which has not the possiblility to continue the script,
# but is much more robust.
proc breakpoint {} {
  puts stderr "Breakpoint! use 'cont' to continue"
  while {1} {
    puts -nonewline stderr "#debug> "
    gets stdin line
    if {$line == "cont"} {break} else {eval $line}
  }
  puts stderr "Resuming Script [info script]"
}

# #############################################################################

proc banner text_to_print {
    puts "\n#############################################"
    puts "# -->  $text_to_print"
    puts "#############################################\n"
}

# #############################################################################
# SNPS: Procedure to display the objects of a collection in single lines
#
# Sep, 2012
#
# example: sld {get_lib_cells tcb018gbwp7twc/SD*}
#   -> prints each result in one line instead of all results in one line
proc sld {args} {

  parse_proc_arguments -args $args command
  echo \n
  set zz [eval $command(pattern)]
  if {[regexp "get_libs*" $command(pattern)] == 1} {
    set xx [sort_collection $zz name]
  } else {
    set xx [sort_collection $zz full_name]
  }  
  foreach_in_collection toto $xx {
    echo [ get_object_name $toto]
  }
  echo "============="
  echo "[sizeof_collection $xx] objects\n"

};
define_proc_attributes sld \
 -info "single line display"\
 -define_args { 
  {pattern "sld get_libs" example string optional}
  {pattern1 "sld get_buffers" example string optional}
  {pattern2 "sld \{get_cells U5\*\}"  example string optional}
  {pattern3 "sld \{get_cells -filter \"name =~ \*reg\*\"\}"  example string optional}
}

proc single_line_display {args} {
  sld $args
}

#############################################################################
# Elmos: Procedure to check the existence of a given file.
#
# Useful in common_setup.tcl for checking the setup.
#
# example: check_file <file>
# If file exists nothing will happen and the flow continues.
# If file is missing you will get an error message like these:
#   Error: Invalid environment, <file> not found
#
proc check_file {file_name } {
    if {! [file exists $file_name] || [file type $file_name] != "file"} {
	puts "Error: Invalid environment, $file_name not found"
	exit 
    }   
}

#############################################################################
# Elmos: Same as check_file just for links
# 
# Useful in common_setup.tcl for checking if link to tech_config.xml is existent
#
proc check_link {file_name } {
    if {! [file exists $file_name] || [file type $file_name] != "link"} {
	puts "Error: Invalid environment, $file_name not found"
	exit 
    }   
}

#############################################################################
# Elmos: Read in a file and return content
# 
# 
#

proc readFromFile {filename} {
    set f [open $filename r]
    set data [read $f]
    close $f
    return $data
}

#############################################################################
# Elmos: select all single vias
#
proc select_single_vias {} {
  change_selection [get_via -filter "row == 1 && col == 1"]
}

