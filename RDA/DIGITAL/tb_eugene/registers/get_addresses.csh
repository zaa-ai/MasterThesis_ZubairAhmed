#!/bin/csh
echo "#####   generate addresses   #####"
set TARGET_PATH = $DESIGN/$DIGITAL/tb_eugene/registers
stove edf-headers --project ${DESIGN}/${DIGITAL}/config/${PROJECT_STATE}.json --strict --flat --template $TARGET_PATH/addresses.vm -o $TARGET_PATH/addresses_pkg.sv -x '#DSI3_wave_shape_registers,#ATPG_test_register,#ELIP_test_register,#SRAM_BIST_test_register,#Standard_test_register,#Test_Register,#Test_Registers,#OTP_ECC_Control_Registers_8bit,#OTP_Key_Register_8bit,#Trimming__OTP_cells_,#SPI_Registers___for_collection_only__,#DSI3_Interface_Registers___for_collection_only__,#DSI3_wave_shaping_registers'
stove edf-headers --project ${DESIGN}/${DIGITAL}/config/${PROJECT_STATE}.json --strict --flat --template $TARGET_PATH/test_addresses.vm -o $TARGET_PATH/test_addresses_pkg.sv -x '#DSI3_wave_shape_registers,#ATPG_test_register,#ELIP_test_register,#SRAM_BIST_test_register,#Standard_test_register,#Test_Register,#Test_Registers,#OTP_ECC_Control_Registers_8bit,#OTP_Key_Register_8bit,#Trimming__OTP_cells_,#SPI_Registers___for_collection_only__,#DSI3_Interface_Registers___for_collection_only__,#DSI3_wave_shaping_registers'
# newline nicht vergessen
