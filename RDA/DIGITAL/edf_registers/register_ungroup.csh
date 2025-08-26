#!/bin/csh
echo "#####   generate ungroup file   #####"
set TARGET_PATH = $DESIGN/$DIGITAL/edf_registers
set EXCLUDE = '#DSI3_wave_shaping_registers,#ELIP_test_register,#SRAM_BIST_test_register,#Standard_test_register,#Trimming__OTP_cells_,#SPI_Registers___for_collection_only__,#DSI3_Interface_Registers___for_collection_only__,#Test_Registers'
stove edf-headers --project ${DESIGN}/${DIGITAL}/config/${PROJECT_STATE}.json --strict --flat --template $TARGET_PATH/ungrouping_template.vm -o $TARGET_PATH/ungroup.tcl -x $EXCLUDE
