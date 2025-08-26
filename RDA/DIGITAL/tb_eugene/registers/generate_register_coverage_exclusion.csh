#!/bin/csh
set TARGET_PATH = $DESIGN/$DIGITAL/tb_eugene/registers
echo "#####   generate func register coverage exclusion   #####"
stove edf-headers --project ${DESIGN}/${DIGITAL}/config/${PROJECT_STATE}.json --strict --flat --template $TARGET_PATH/register_coverage_exclusion.vm -o $TARGET_PATH/func_registers.el --arguments category=func excludeTable=DSI3_wave_shaping_registers
echo "#####   generate test register coverage exclusion   #####"
stove edf-headers --project ${DESIGN}/${DIGITAL}/config/${PROJECT_STATE}.json --strict --flat --template $TARGET_PATH/register_coverage_exclusion.vm -o $TARGET_PATH/test_registers.el --arguments category=test excludeTable=JTAG_standard_registers,Test_Registers
# newline nicht vergessen
