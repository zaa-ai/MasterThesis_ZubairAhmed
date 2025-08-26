#!/bin/csh
echo "#####   generate c headers   #####"
stove edf-headers -p ${DESIGN}/${DIGITAL}/config/${PROJECT_STATE}.json -t ${DESIGN}/${DIGITAL}/config/c_headers.vm -o ${DESIGN}/${DIGITAL}/config/c_headers.c -f --arguments category=func project=${PROJECT_STATE}
