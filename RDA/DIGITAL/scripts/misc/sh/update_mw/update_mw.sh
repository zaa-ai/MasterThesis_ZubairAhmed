#!/bin/bash
source /etc/bashrc
source /etc/profile
module use /common/run/synopsys/modules
module load dc/H-2013.03-SP4
module load milkyway

if [ $# -ne 2 ] || [ ! -d $1 ] || [ ! -f $2 ]; then
    echo "Wrong arguments!"
    echo "Usage: $0 <MW> <Liberty>"
    exit
fi

mw=`basename $1`_upd
libname=`basename $2 .lib`_upd
lib=${libname}.lib

# Copy MW and Liberty to the current dir
cp -r $1 $mw
cp $2 $lib

# Replace 'routing_pin' by 'device_layer'
sed -i 's/physical_connection\s*:\s*routing_pin\s*;/physical_connection : device_layer ;/' $lib

# Generate new db
echo "Convert $lib"
lc_shell <<EOF
suppress_message { LBDB-607  LBDB-887 LBDB-301 LIBG-10 LBDB-272 LBDB-1054 LIBG-10 LIBG-205 LIBG-41 LIBG-265 LIBG-275 }
read_lib $lib > $libname.log
write_lib [get_object_name [get_libs]] -format db -output $libname.db
report_lib [get_object_name [get_libs]] > $libname.db.report
EOF

# Update MW using new db
cat > mw.tcl <<EOF
update_mw_port_by_db -mw_lib $mw -db_file $libname.db -bias_pg
exit
EOF

Milkyway -tcl -file mw.tcl -cmd As.tcl -log mw.log -nogui


# Run Milkyway:
# > Milkyway -trueColor
#
# Choose 'Output' menu
#  and 'LEF Out ..'
