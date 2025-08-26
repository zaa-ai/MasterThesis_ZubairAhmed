#!/bin/csh
echo "#####   downloading database   #####"
rm -rf ${DESIGN}/${DIGITAL}/config/${PROJECT_STATE}.json
stove edf-get-structure -p ${PROJECT_STATE} -o ${DESIGN}/${DIGITAL}/config/${PROJECT_STATE}.json
