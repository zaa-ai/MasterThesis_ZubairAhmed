`ifndef _ADDRESSES_PKG
`define _ADDRESSES_PKG
/*==================================================
 *  Copyright (c) 2023 Elmos SE
 *  Author: stove
 *  Description : Note: This file has been generated automatically by stove
 *                Note: This file should not be modified manually.
 *                This file contains all functional register addresses as constants and an associative array for register naming
 *==================================================*/
package addresses_pkg;
// @SuppressProblem -nowarnmiss 1 -type fully_unread_static_variable -count 100 -length 100
	parameter int ADDR_INFO_IC_REVISION = 'h1f; /* Revision of the IC */
	parameter int ADDR_INFO_CHIP_ID_LOW = 'h1; /* Chip identification - lower word */
	parameter int ADDR_INFO_CHIP_ID_HIGH = 'h2; /* Chip identification - upper word */
	parameter int ADDR_SUPPLY_TRIM_IREF = 'h3; /* trim register for reference current */
	parameter int ADDR_SUPPLY_TRIM_OT = 'h4; /* trim register for overtemperature adaption */
	parameter int ADDR_SUPPLY_SUP_HW_CTRL = 'h3c; /* control register for DSI3 supply
 */
	parameter int ADDR_SUPPLY_SUP_IRQ_STAT = 'h3a; /* supply interrupt status register */
	parameter int ADDR_SUPPLY_SUP_IRQ_MASK = 'h3b; /* supply interrupt mask register */
	parameter int ADDR_SUPPLY_SUP_STAT = 'h3d; /* DSI3 supply status register */
	parameter int ADDR_SUPPLY_SUP_CTRL = 'h3e; /* control register for DSI3 supply
 */
	parameter int ADDR_SUPPLY_IO_CTRL = 'h3f; /* digital IO pads control register */
	parameter int ADDR_TIMEBASE_CLKREF_CONF = 'h40; /* timebase configuration register
 */
	parameter int ADDR_TIMEBASE_TB_CNT = 'h41; /* timebase counter register */
	parameter int ADDR_TIMEBASE_TRIM_OSC = 'h6; /* trim value of oscillator */
	parameter int ADDR_TIMEBASE_TRIM_OSC_TCF = 'h7; /* temperature dependency trim value of oscillator */
	parameter int ADDR_INTERRUPT_IRQ_STAT = 'h50; /* interrupt status register */
	parameter int ADDR_INTERRUPT_IRQ_MASK = 'h51; /* interrupt mask register */
	parameter int ADDR_INTERRUPT_ECC_IRQ_STAT = 'h52; /* ECC failure interrupt status register */
	parameter int ADDR_INTERRUPT_ECC_IRQ_MASK = 'h53; /* ECC failure interrupt mask register */
	parameter int ADDR_INTERRUPT_ECC_CORR_IRQ_STAT = 'h54; /* ECC correction interrupt status register */
	parameter int ADDR_INTERRUPT_ECC_CORR_IRQ_MASK = 'h55; /* ECC correction interrupt mask register */
	parameter int ADDR_BUFFER_IRQS_BUF_IRQ_STAT = 'h61; /* ring buffer interrupt register */
	parameter int ADDR_BUFFER_IRQS_BUF_IRQ_MASK = 'h62; /* ring buffer interrupt mask register */
	parameter int ADDR_BUFFER_IRQS_BUF_FILL_WARN = 'h63; /* buffer fill warning register */
	parameter int ADDR_SPI_SPI_IRQ_STAT = 'h80; /* SPI interrupt status register */
	parameter int ADDR_SPI_SPI_IRQ_MASK = 'h81; /* SPI interrupt mask register */
	parameter int ADDR_SPI_STATUS_WORD = 'h85; /* IC status word */
	parameter int ADDR_DSI_COMMON_DSI_ENABLE = 'h91; /* configuration of DSI3 transceiver */
	parameter int ADDR_DSI_COMMON_DSI_CFG = 'h92; /* common configuration of DSI3 transceivers */
	parameter int ADDR_DSI_COMMON_DSI_TX_SHIFT = 'h94; /* start time difference between the leading edges of DSI channel transmit pulses */
	parameter int ADDR_DSI_COMMON_SYNC_IDLE_REG = 'h95; /* Idle information for synchronization of DSI3 channels */
	parameter int ADDR_DSI_COMMON_CRM_TIME = 'h98; /* time of the CRM command */
	parameter int ADDR_DSI_COMMON_CRM_TIME_NR = 'h99; /* time of the CRM command without response */
	parameter int ADDR_OTP_CTRL_OTP_READ_ADDRESS = 'h70; /* Address of OTP cell to read */
	parameter int ADDR_OTP_CTRL_OTP_READ_VALUE = 'h71; /* Value of previous OTP read access */
	parameter int ADDR_OTP_CTRL_OTP_READ_STATUS = 'h72; /* Status of the OTP read operation */
	parameter int ADDR_DSI_TRIMMING_0_TRIM_DSI_REC_FALL = 'h10; /* Trimming register for DSI receiver falling edge */
	parameter int ADDR_DSI_TRIMMING_0_TRIM_DSI_REC_RISE = 'h11; /* Trimming register for DSI receiver rising edge */
	parameter int ADDR_DSI_TRIMMING_1_TRIM_DSI_REC_FALL = 'h12; /* Trimming register for DSI receiver falling edge */
	parameter int ADDR_DSI_TRIMMING_1_TRIM_DSI_REC_RISE = 'h13; /* Trimming register for DSI receiver rising edge */
	parameter int ADDR_DSI_0_DSI_STAT = 'ha0; /* DSI3 status */
	parameter int ADDR_DSI_0_PDCM_PERIOD = 'ha4; /* DSI3 PDCM period configuration */
	parameter int ADDR_DSI_0_DSI_LOAD = 'ha5; /* load current of this DSI3 channel */
	parameter int ADDR_DSI_0_DSI_IRQ_STAT = 'ha8; /* IRQ status register */
	parameter int ADDR_DSI_0_DSI_IRQ_MASK = 'ha9; /* DSI channel IRQ mask register */
	parameter int ADDR_DSI_0_DSI_CMD = 'hb0; /* (SPI) command in execution */
	parameter int ADDR_DSI_0_CRM_WORD2 = 'hb1; /* CRM command (lower word) */
	parameter int ADDR_DSI_0_CRM_WORD1 = 'hb2; /* CRM command (higher word) */
	parameter int ADDR_DSI_0_PACKET_STAT = 'hb8; /* current status of the DSI3 package in reception */
	parameter int ADDR_DSI_0_FRAME_STAT = 'hbb; /* current status of PDCM frame in reception */
	parameter int ADDR_DSI_0_WAIT_TIME = 'hb9; /* remaining wait time (in µs) */
	parameter int ADDR_DSI_0_SYNC = 'hba; /* current synchronization channel selection for synchronization */
	parameter int ADDR_DSI_1_DSI_STAT = 'hc0; /* DSI3 status */
	parameter int ADDR_DSI_1_PDCM_PERIOD = 'hc4; /* DSI3 PDCM period configuration */
	parameter int ADDR_DSI_1_DSI_LOAD = 'hc5; /* load current of this DSI3 channel */
	parameter int ADDR_DSI_1_DSI_IRQ_STAT = 'hc8; /* IRQ status register */
	parameter int ADDR_DSI_1_DSI_IRQ_MASK = 'hc9; /* DSI channel IRQ mask register */
	parameter int ADDR_DSI_1_DSI_CMD = 'hd0; /* (SPI) command in execution */
	parameter int ADDR_DSI_1_CRM_WORD2 = 'hd1; /* CRM command (lower word) */
	parameter int ADDR_DSI_1_CRM_WORD1 = 'hd2; /* CRM command (higher word) */
	parameter int ADDR_DSI_1_PACKET_STAT = 'hd8; /* current status of the DSI3 package in reception */
	parameter int ADDR_DSI_1_FRAME_STAT = 'hdb; /* current status of PDCM frame in reception */
	parameter int ADDR_DSI_1_WAIT_TIME = 'hd9; /* remaining wait time (in µs) */
	parameter int ADDR_DSI_1_SYNC = 'hda; /* current synchronization channel selection for synchronization */
	parameter int ADDR_SPI_CMD_STAT_BUF_VALID_COUNT = 'h100; /* number of valid data words in the buffer */
	parameter int ADDR_SPI_CMD_STAT_BUF_FREE = 'h102; /* number of currently free memory cells */
	parameter int ADDR_SPI_CMD_STAT_BUF_READ_POINTER = 'h108; /* value of the read pointer */
	parameter int ADDR_SPI_CMD_STAT_BUF_WRITE_POINTER = 'h109; /* value of the write pointer */
	parameter int ADDR_SPI_CMD_STAT_BUF_VALID_POINTER = 'h10a; /* value of the valid pointer */
	parameter int ADDR_DSI_CMD_STAT_0_BUF_VALID_COUNT = 'h110; /* number of valid data words in the buffer */
	parameter int ADDR_DSI_CMD_STAT_0_BUF_FREE = 'h112; /* number of currently free memory cells */
	parameter int ADDR_DSI_CMD_STAT_0_BUF_READ_POINTER = 'h118; /* value of the read pointer */
	parameter int ADDR_DSI_CMD_STAT_0_BUF_WRITE_POINTER = 'h119; /* value of the write pointer */
	parameter int ADDR_DSI_CMD_STAT_0_BUF_VALID_POINTER = 'h11a; /* value of the valid pointer */
	parameter int ADDR_DSI_CMD_STAT_1_BUF_VALID_COUNT = 'h120; /* number of valid data words in the buffer */
	parameter int ADDR_DSI_CMD_STAT_1_BUF_FREE = 'h122; /* number of currently free memory cells */
	parameter int ADDR_DSI_CMD_STAT_1_BUF_READ_POINTER = 'h128; /* value of the read pointer */
	parameter int ADDR_DSI_CMD_STAT_1_BUF_WRITE_POINTER = 'h129; /* value of the write pointer */
	parameter int ADDR_DSI_CMD_STAT_1_BUF_VALID_POINTER = 'h12a; /* value of the valid pointer */
	parameter int ADDR_DSI_CRM_STAT_0_BUF_VALID_COUNT = 'h130; /* number of valid data words in the buffer */
	parameter int ADDR_DSI_CRM_STAT_0_BUF_FREE = 'h132; /* number of currently free memory cells */
	parameter int ADDR_DSI_CRM_STAT_0_BUF_READ_POINTER = 'h138; /* value of the read pointer */
	parameter int ADDR_DSI_CRM_STAT_0_BUF_WRITE_POINTER = 'h139; /* value of the write pointer */
	parameter int ADDR_DSI_CRM_STAT_0_BUF_VALID_POINTER = 'h13a; /* value of the valid pointer */
	parameter int ADDR_DSI_CRM_STAT_1_BUF_VALID_COUNT = 'h140; /* number of valid data words in the buffer */
	parameter int ADDR_DSI_CRM_STAT_1_BUF_FREE = 'h142; /* number of currently free memory cells */
	parameter int ADDR_DSI_CRM_STAT_1_BUF_READ_POINTER = 'h148; /* value of the read pointer */
	parameter int ADDR_DSI_CRM_STAT_1_BUF_WRITE_POINTER = 'h149; /* value of the write pointer */
	parameter int ADDR_DSI_CRM_STAT_1_BUF_VALID_POINTER = 'h14a; /* value of the valid pointer */
	parameter int ADDR_DSI_PDCM_STAT_0_BUF_VALID_COUNT = 'h150; /* number of valid data words in the buffer */
	parameter int ADDR_DSI_PDCM_STAT_0_BUF_FREE = 'h152; /* number of currently free memory cells */
	parameter int ADDR_DSI_PDCM_STAT_0_BUF_READ_POINTER = 'h158; /* value of the read pointer */
	parameter int ADDR_DSI_PDCM_STAT_0_BUF_WRITE_POINTER = 'h159; /* value of the write pointer */
	parameter int ADDR_DSI_PDCM_STAT_0_BUF_VALID_POINTER = 'h15a; /* value of the valid pointer */
	parameter int ADDR_DSI_PDCM_STAT_1_BUF_VALID_COUNT = 'h160; /* number of valid data words in the buffer */
	parameter int ADDR_DSI_PDCM_STAT_1_BUF_FREE = 'h162; /* number of currently free memory cells */
	parameter int ADDR_DSI_PDCM_STAT_1_BUF_READ_POINTER = 'h168; /* value of the read pointer */
	parameter int ADDR_DSI_PDCM_STAT_1_BUF_WRITE_POINTER = 'h169; /* value of the write pointer */
	parameter int ADDR_DSI_PDCM_STAT_1_BUF_VALID_POINTER = 'h16a; /* value of the valid pointer */

	const string addresses[int]='{
		'h1f : "INFO_IC_REVISION",	
		'h1 : "INFO_CHIP_ID_LOW",	
		'h2 : "INFO_CHIP_ID_HIGH",	
		'h3 : "SUPPLY_TRIM_IREF",	
		'h4 : "SUPPLY_TRIM_OT",	
		'h3c : "SUPPLY_SUP_HW_CTRL",	
		'h3a : "SUPPLY_SUP_IRQ_STAT",	
		'h3b : "SUPPLY_SUP_IRQ_MASK",	
		'h3d : "SUPPLY_SUP_STAT",	
		'h3e : "SUPPLY_SUP_CTRL",	
		'h3f : "SUPPLY_IO_CTRL",	
		'h40 : "TIMEBASE_CLKREF_CONF",	
		'h41 : "TIMEBASE_TB_CNT",	
		'h6 : "TIMEBASE_TRIM_OSC",	
		'h7 : "TIMEBASE_TRIM_OSC_TCF",	
		'h50 : "INTERRUPT_IRQ_STAT",	
		'h51 : "INTERRUPT_IRQ_MASK",	
		'h52 : "INTERRUPT_ECC_IRQ_STAT",	
		'h53 : "INTERRUPT_ECC_IRQ_MASK",	
		'h54 : "INTERRUPT_ECC_CORR_IRQ_STAT",	
		'h55 : "INTERRUPT_ECC_CORR_IRQ_MASK",	
		'h61 : "BUFFER_IRQS_BUF_IRQ_STAT",	
		'h62 : "BUFFER_IRQS_BUF_IRQ_MASK",	
		'h63 : "BUFFER_IRQS_BUF_FILL_WARN",	
		'h80 : "SPI_SPI_IRQ_STAT",	
		'h81 : "SPI_SPI_IRQ_MASK",	
		'h85 : "SPI_STATUS_WORD",	
		'h91 : "DSI_COMMON_DSI_ENABLE",	
		'h92 : "DSI_COMMON_DSI_CFG",	
		'h94 : "DSI_COMMON_DSI_TX_SHIFT",	
		'h95 : "DSI_COMMON_SYNC_IDLE_REG",	
		'h98 : "DSI_COMMON_CRM_TIME",	
		'h99 : "DSI_COMMON_CRM_TIME_NR",	
		'h70 : "OTP_CTRL_OTP_READ_ADDRESS",	
		'h71 : "OTP_CTRL_OTP_READ_VALUE",	
		'h72 : "OTP_CTRL_OTP_READ_STATUS",	
		'h10 : "DSI_TRIMMING_0_TRIM_DSI_REC_FALL",	
		'h11 : "DSI_TRIMMING_0_TRIM_DSI_REC_RISE",	
		'h12 : "DSI_TRIMMING_1_TRIM_DSI_REC_FALL",	
		'h13 : "DSI_TRIMMING_1_TRIM_DSI_REC_RISE",	
		'ha0 : "DSI_0_DSI_STAT",	
		'ha4 : "DSI_0_PDCM_PERIOD",	
		'ha5 : "DSI_0_DSI_LOAD",	
		'ha8 : "DSI_0_DSI_IRQ_STAT",	
		'ha9 : "DSI_0_DSI_IRQ_MASK",	
		'hb0 : "DSI_0_DSI_CMD",	
		'hb1 : "DSI_0_CRM_WORD2",	
		'hb2 : "DSI_0_CRM_WORD1",	
		'hb8 : "DSI_0_PACKET_STAT",	
		'hbb : "DSI_0_FRAME_STAT",	
		'hb9 : "DSI_0_WAIT_TIME",	
		'hba : "DSI_0_SYNC",	
		'hc0 : "DSI_1_DSI_STAT",	
		'hc4 : "DSI_1_PDCM_PERIOD",	
		'hc5 : "DSI_1_DSI_LOAD",	
		'hc8 : "DSI_1_DSI_IRQ_STAT",	
		'hc9 : "DSI_1_DSI_IRQ_MASK",	
		'hd0 : "DSI_1_DSI_CMD",	
		'hd1 : "DSI_1_CRM_WORD2",	
		'hd2 : "DSI_1_CRM_WORD1",	
		'hd8 : "DSI_1_PACKET_STAT",	
		'hdb : "DSI_1_FRAME_STAT",	
		'hd9 : "DSI_1_WAIT_TIME",	
		'hda : "DSI_1_SYNC",	
		'h100 : "SPI_CMD_STAT_BUF_VALID_COUNT",	
		'h102 : "SPI_CMD_STAT_BUF_FREE",	
		'h108 : "SPI_CMD_STAT_BUF_READ_POINTER",	
		'h109 : "SPI_CMD_STAT_BUF_WRITE_POINTER",	
		'h10a : "SPI_CMD_STAT_BUF_VALID_POINTER",	
		'h110 : "DSI_CMD_STAT_0_BUF_VALID_COUNT",	
		'h112 : "DSI_CMD_STAT_0_BUF_FREE",	
		'h118 : "DSI_CMD_STAT_0_BUF_READ_POINTER",	
		'h119 : "DSI_CMD_STAT_0_BUF_WRITE_POINTER",	
		'h11a : "DSI_CMD_STAT_0_BUF_VALID_POINTER",	
		'h120 : "DSI_CMD_STAT_1_BUF_VALID_COUNT",	
		'h122 : "DSI_CMD_STAT_1_BUF_FREE",	
		'h128 : "DSI_CMD_STAT_1_BUF_READ_POINTER",	
		'h129 : "DSI_CMD_STAT_1_BUF_WRITE_POINTER",	
		'h12a : "DSI_CMD_STAT_1_BUF_VALID_POINTER",	
		'h130 : "DSI_CRM_STAT_0_BUF_VALID_COUNT",	
		'h132 : "DSI_CRM_STAT_0_BUF_FREE",	
		'h138 : "DSI_CRM_STAT_0_BUF_READ_POINTER",	
		'h139 : "DSI_CRM_STAT_0_BUF_WRITE_POINTER",	
		'h13a : "DSI_CRM_STAT_0_BUF_VALID_POINTER",	
		'h140 : "DSI_CRM_STAT_1_BUF_VALID_COUNT",	
		'h142 : "DSI_CRM_STAT_1_BUF_FREE",	
		'h148 : "DSI_CRM_STAT_1_BUF_READ_POINTER",	
		'h149 : "DSI_CRM_STAT_1_BUF_WRITE_POINTER",	
		'h14a : "DSI_CRM_STAT_1_BUF_VALID_POINTER",	
		'h150 : "DSI_PDCM_STAT_0_BUF_VALID_COUNT",	
		'h152 : "DSI_PDCM_STAT_0_BUF_FREE",	
		'h158 : "DSI_PDCM_STAT_0_BUF_READ_POINTER",	
		'h159 : "DSI_PDCM_STAT_0_BUF_WRITE_POINTER",	
		'h15a : "DSI_PDCM_STAT_0_BUF_VALID_POINTER",	
		'h160 : "DSI_PDCM_STAT_1_BUF_VALID_COUNT",	
		'h162 : "DSI_PDCM_STAT_1_BUF_FREE",	
		'h168 : "DSI_PDCM_STAT_1_BUF_READ_POINTER",	
		'h169 : "DSI_PDCM_STAT_1_BUF_WRITE_POINTER",	
		'h16a : "DSI_PDCM_STAT_1_BUF_VALID_POINTER"	
	};

endpackage : addresses_pkg

`endif
	