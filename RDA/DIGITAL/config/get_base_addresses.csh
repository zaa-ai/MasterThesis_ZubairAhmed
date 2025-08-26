#!/bin/csh
echo "#####   generate base address file   #####"
stove edf-headers -p ${DESIGN}/${DIGITAL}/config/${PROJECT_STATE}.json -o ${DESIGN}/${DIGITAL}/config/base_addresses.sv -t ${DESIGN}/${DIGITAL}/config/base_addresses.vm -f --arguments category=func
stove edf-headers -p ${DESIGN}/${DIGITAL}/config/${PROJECT_STATE}.json -o ${DESIGN}/${DIGITAL}/config/base_addresses_test.sv -t ${DESIGN}/${DIGITAL}/config/base_addresses.vm -f --arguments category=test
# newline nicht vergessen
