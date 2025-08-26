#!/bin/csh
echo "#####   generate EPM model   #####"
set TARGET_PATH = $DESIGN/$DIGITAL/tb_eugene/epms
stove edf-headers --project ${DESIGN}/${DIGITAL}/config/${PROJECT_STATE}.json --strict --flat --template $TARGET_PATH/edf_epm_model.vm -o $TARGET_PATH/edf_epm_model_pkg.sv
# newline nicht vergessen
