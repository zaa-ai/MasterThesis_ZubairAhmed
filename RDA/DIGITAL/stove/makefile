
VTL_FILES = $(shell find . -name "*.vm")

EXCLUDES = '#ADC__Measurement_Control__Registers,#CAL_CLOCK_CTRL,#CAL_SFL_CTRL,#CAL_SYS_STATE,#CLOCK_CTRL_Registers,#SFL_CTRL_Configuration_Registers,#SFL_CTRL_DCT_Registers,#CRC16_Registers,#SW_DP_Registers,#TEST_AP_Registers,#SFL_CTRL_Registers,#Funclet_Parameter,#GPIO_Registers,#WDOG_Registers,#SFL_CTRL_Version_Register,#TIMER_Registers,#SWTIMER_Registers,#SYS_STATE_Registers,#LIN_CTRL_Registers,#LINSCI_Registers,#SFL_CTRL_Mode_Registers,#SFL_CTRL_Write_Address_Registers,#SFL_CTRL_Write_Data_Registers,#SFL_CTRL_Command_Registers,#SFL_CTRL_Protection_Select_Registers,#SFL_CTRL_Protection_Registers,#PWM_Control_Registers,#RESET_CTRL_Registers,#Test_Register_for_Peripheral_Blocks,#SFL_CTRL_Test_Registers,#TEST_LOGIC_CoreSys_Test_Registers,#HB__Half_Bridge_Control__Registers,#HALL_SENS_CTRL__Hall_Sensor_Control__Registers,#SUP__Operation_Mode_Control__Registers'

$(VTL_FILES) : 
	VTL_NAME = $(shell basename $@)
	echo "$(VTL_NAME)"

files : $(VTL_FILES)
