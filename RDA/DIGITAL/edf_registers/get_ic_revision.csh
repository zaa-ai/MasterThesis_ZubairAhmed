#!/bin/csh
echo "#####  get revision from svn_revision_inc.sv  #####"
setenv IC_REVISION `egrep "[0-9]{4}" $DESIGN/$DIGITAL/edf_registers/svn_revision_inc.sv -o`

echo "######################################"
echo "IC_REVISION is $IC_REVISION"
echo "######################################"
