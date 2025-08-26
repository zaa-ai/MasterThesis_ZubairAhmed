#!/bin/csh
echo "#####   generate RAL description   #####"
set TARGET_PATH = $DESIGN/$DIGITAL/tb_eugene/registers
set EXCLUDE = '#DSI3_Wave_shape_registers,#ATPG_test_register,#ELIP_test_register,#SRAM_BIST_test_register,#Standard_test_register,#Test_Register,#Test_Registers,#OTP_ECC_Control_Registers_8bit,#OTP_Key_Register_8bit,#Trimming__OTP_cells_,#SPI_Registers___for_collection_only__,#DSI3_Interface_Registers___for_collection_only__'
stove edf-headers --project ${DESIGN}/${DIGITAL}/config/${PROJECT_STATE}.json --strict --flat --template $TARGET_PATH/ral_template.vm -o $TARGET_PATH/registers.ral -x $EXCLUDE
echo "#####   generate RAL description for test   #####"
stove edf-headers --project ${DESIGN}/${DIGITAL}/config/${PROJECT_STATE}.json --strict --flat --template $TARGET_PATH/ral_template_test.vm -o $TARGET_PATH/test_registers.ral -x $EXCLUDE
# newline nicht vergessen
