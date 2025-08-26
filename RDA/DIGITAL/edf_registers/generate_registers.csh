#!/bin/csh
echo "#####   generate registers   #####"
rm -rf $DESIGN/$DIGITAL/edf_registers/*.sv
stove edf-hdl -p ${DESIGN}/${DIGITAL}/config/${PROJECT_STATE}.json -o $DESIGN/$DIGITAL/edf_registers/.
