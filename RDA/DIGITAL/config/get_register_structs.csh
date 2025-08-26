#!/bin/csh
echo "#####   generate register structs   #####"
set TARGET_PATH = $DESIGN/$DIGITAL/config
stove edf-headers --project ${DESIGN}/${DIGITAL}/config/${PROJECT_STATE}.json --strict --flat --template $TARGET_PATH/register_structs.vm -o $TARGET_PATH/register_structs.sv -x '#DSI3_wave_shape_registers,#ATPG_test_register,#ELIP_test_register,#SRAM_BIST_test_register,#Standard_test_register,#Test_Register,#Test_Registers,#OTP_ECC_Control_Registers_8bit,#OTP_Key_Register_8bit,#Trimming__OTP_cells_,#SPI_Registers___for_collection_only__,#DSI3_Interface_Registers___for_collection_only__,#DSI3_wave_shaping_registers'
echo "#####   generate test register structs   #####"
stove edf-headers --project ${DESIGN}/${DIGITAL}/config/${PROJECT_STATE}.json --strict --flat --template $TARGET_PATH/test_register_structs.vm -o $TARGET_PATH/test_register_structs.sv -x '#DSI3_wave_shape_registers,#ATPG_test_register,#ELIP_test_register,#SRAM_BIST_test_register,#Standard_test_register,#Test_Register,#Test_Registers,#OTP_ECC_Control_Registers_8bit,#OTP_Key_Register_8bit,#Trimming__OTP_cells_,#SPI_Registers___for_collection_only__,#DSI3_Interface_Registers___for_collection_only__,#DSI3_wave_shaping_registers'
# newline nicht vergessen
