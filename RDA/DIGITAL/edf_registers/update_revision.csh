#!/bin/csh
echo "#####   update revision   #####"
setenv GIT_REVISION `git rev-list --all --count`
rm -rf $DESIGN/$DIGITAL/edf_registers/svn_revision_inc.sv
echo '`'"define SVN_REVISION 16'd"$GIT_REVISION > $DESIGN/$DIGITAL/edf_registers/svn_revision_inc.sv

echo "######################################"
echo "IC_REVISION is $GIT_REVISION"
echo "######################################"
