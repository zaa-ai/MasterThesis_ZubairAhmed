
foreach cell [list DCAPBWP7T DCAP4BWP7T DCAP8BWP7T DCAP16BWP7T DCAP32BWP7T DCAP64BWP7T GDCAPBWP7T GDCAP2BWP7T GDCAP3BWP7T GDCAP4BWP7T GDCAP10BWP7T] {
  eval "set ${cell}_count [sizeof_collection [get_flat_cells -all -filter "ref_name == $cell"]]"
}

# values from: ~mns/bin/digicells-t7.txt
set decoup     [expr $DCAPBWP7T_count    * 4.2   + \
                     $DCAP4BWP7T_count   * 9.5   + \
                     $DCAP8BWP7T_count   * 43.4  + \
                     $DCAP16BWP7T_count  * 98.3  + \
                     $DCAP32BWP7T_count  * 210.0 + \
                     $DCAP64BWP7T_count  * 438.9 + \
                     $GDCAPBWP7T_count   * 4.2   + \
                     $GDCAP2BWP7T_count  * 8.4   + \
                     $GDCAP3BWP7T_count  * 12.5  + \
                     $GDCAP4BWP7T_count  * 16.7  + \
                     $GDCAP10BWP7T_count * 41.8    ]

puts "Decoupling capacitance: $decoup fF" 
