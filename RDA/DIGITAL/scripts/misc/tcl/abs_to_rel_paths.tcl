# This script can be used to change all the absolute paths in
# digital.autoread.tcl to relative paths and print it in an output file.

# Created by Makarand Potdar
# Created on 11/11/2019
# Adapted by Markus Winkler
# Adapted on 10/01/2022

# Run this script from the working directory from which the analyze command was run
# Provide the input file name followed by output file name as command line arguments
# This script might fail if the current working hierarchy contains repeated folder names
# For example, suppose the current working directory path is /home/..../rtl/new/scripts
# And the there are files in multiple folders, for example /home/...../rtl/code1.v and /home/...../rtl/new/rtl/code2.v
# In such cases this script might give incorrect output

# Get the current working directory and split it's hierarchy
set current_dir [pwd]
set curr_dir_hier [split $current_dir /]
set hier_len [llength $curr_dir_hier]

# Provide the input and output file names as command line arguments
set infile [open [lindex $argv 0] r]
set outfile [open [lindex $argv 1] w]
# open a temporary file 
set tmpfile [open tempfile w]

# Read the input file line for line
while { [gets $infile data] >= 0} {

# Sometimes the line contains two pathes (because the autroread.tcl contains these)
# So we split up these lines and write them down in the temp file
    if [regexp {lib[name|rary] *.* \{\s?(((/.*)*/(.*))[\s]((/.*)*/(.*[\s])))} $data a both_paths abs_path1 x filename1 abs_path2 y filename2] {
        regsub $both_paths $data " $abs_path1 " data1
        puts $tmpfile $data1
        regsub $both_paths $data " $abs_path2 " data2
        puts $tmpfile $data2
        } else {
    # Otherwise write unmodified data to tempfile
        puts $tmpfile $data
    }
}
close $tmpfile
close $infile

# Open the tempfile again for reading and read it in line for line,
# now with only single paths
set tmpfile [open tempfile r]
while { [gets $infile data] >= 0} {

# Search for "define_design_lib <LIBNAME> -path <abs_path> and replace <abs_path> with relative one
if [regexp {define_design_lib[\s].*[\s]-path[\s](/.*/(.*))} $data -> abs_path foldername] {

        set rel_path "$foldername"

        # Iterate the current working directory hierarchy to get folders
        for {set i [expr $hier_len-1]} {$i >= 0} {incr i -1} {

            # Check If the folder name matches in absolute path
            if [regexp ([lindex $curr_dir_hier//  $i]) $abs_path common_hier] {
        
                # Check if there are any others folders in the absolute path after the matched folder
                if [regexp $common_hier/(.*)/$foldername $abs_path d folders] {

                    # Substitute the file name with the path after the matched folder   
                    regsub $foldername $rel_path "$folders/$foldername" rel_path
                }
                # Substitute the absolute path with the relative path and print it in the file
                regsub $abs_path $data $rel_path data1
                puts $outfile $data1
                break

            # If the folder name does not match
            } else {

            # Set rel_path to previous hierarchy and set the rel_path variable accordingly
            set rel_path "../$rel_path"
        }
    }

# Search for "WORK { pathname } from the input file
# Modify it according to your requirements
} elseif [regexp {lib[name|rary] *.* \{\s?((/.*)*/(.*)[\s])} $data a abs_path x filename] {
       # Separate the file name and set variable rel_path to filename
        set rel_path "$filename"

        # Iterate the current working directory hierarchy to get folders
        for {set i [expr $hier_len-1]} {$i >= 0} {incr i -1} {

            # Check If the folder name matches in absolute path
            if [regexp ([lindex $curr_dir_hier//  $i]) $abs_path common_hier] {
        
                # Check if there are any others folders in the absolute path after the matched folder
                if [regexp $common_hier/(.*)/$filename $abs_path d folders] {

                    # Substitute the file name with the path after the matched folder   
                    regsub $filename $rel_path "$folders/$filename" rel_path
                }
                # Substitute the absolute path with the relative path and print it in the file
                regsub $abs_path $data $rel_path data1
                puts $outfile $data1
                break

            # If the folder name does not match
            } else {

            # Set rel_path to previous hierarchy and set the rel_path variable accordingly
            set rel_path "../$rel_path"
        }
    }
 

# In case there is no match in the first loop, print the line as is in the output file
# Other cases could be added e.g. for the 
} else {
puts $outfile $data
}
}

# Close the files
close $tmpfile
close $outfile

# delete the tempfile
file delete tempfile

