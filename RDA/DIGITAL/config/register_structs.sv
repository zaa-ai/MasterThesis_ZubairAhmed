
`ifndef _REGISTER_STRUCTS
`define _REGISTER_STRUCTS

	typedef struct packed unsigned {
		logic[15:0] REVISION;
	} IC_REVISION_t;
	
	typedef struct packed unsigned {
		logic[15:0] CHIP_ID_LOW;
	} CHIP_ID_LOW_t;
	
	typedef struct packed unsigned {
		logic[15:0] CHIP_ID_HIGH;
	} CHIP_ID_HIGH_t;
	
	typedef struct packed unsigned {
		logic[11:0] unused_1;
		logic[3:0] IREF;
	} TRIM_IREF_t;
	
	typedef struct packed unsigned {
		logic[13:0] unused_1;
		logic[1:0] TRIM_OT;
	} TRIM_OT_t;
	
	typedef struct packed unsigned {
		logic[13:0] unused_1;
		logic IGNORE_HWF;
		logic IGNORE_UV;
	} SUP_HW_CTRL_t;
	
	typedef struct packed unsigned {
		logic OTW;
		logic OTE;
		logic LDOUV;
		logic VCCUV;
		logic REF_FAIL;
	} SUP_IRQ_STAT_t;
	
	typedef struct packed unsigned {
		logic OTW;
		logic OTE;
		logic LDOUV;
		logic VCCUV;
		logic REF_FAIL;
	} SUP_IRQ_MASK_t;
	
	typedef struct packed unsigned {
		logic OTW;
		logic OTE;
		logic LDOUV;
		logic VCCUV;
		logic REF_FAIL;
	} SUP_STAT_t;
	
	typedef struct packed unsigned {
		logic EN_LDO;
	} SUP_CTRL_t;
	
	typedef struct packed unsigned {
		logic HICUR;
	} IO_CTRL_t;
	
	typedef struct packed unsigned {
		logic[1:0] TRE;
	} DSI_ENABLE_t;
	
	typedef struct packed unsigned {
		logic SYNC_MASTER;
		logic SYNC_PDCM;
		logic CRC_EN;
		logic[1:0] BITTIME;
		logic[1:0] CHIPTIME;
	} DSI_CFG_t;
	
	typedef struct packed unsigned {
		logic[6:0] SHIFT;
	} DSI_TX_SHIFT_t;
	
	typedef struct packed unsigned {
		logic PIN;
		logic[12:0] unused_1;
		logic[1:0] DSI;
	} SYNC_IDLE_REG_t;
	
	typedef struct packed unsigned {
		logic[4:0] unused_1;
		logic[10:0] TIME;
	} CRM_TIME_t;
	
	typedef struct packed unsigned {
		logic[4:0] unused_1;
		logic[10:0] TIME;
	} CRM_TIME_NR_t;
	
	typedef struct packed unsigned {
		logic[3:0] SLAVES;
		logic SYNC;
		logic DSIUV;
		logic DSIOV;
		logic[7:0] PULSECNT;
	} DSI_STAT_t;
	
	typedef struct packed unsigned {
		logic[15:0] PDCMPER;
	} PDCM_PERIOD_t;
	
	typedef struct packed unsigned {
		logic START_MEASUREMENT;
		logic IDLE;
		logic[8:0] unused_1;
		logic[4:0] LOAD;
	} DSI_LOAD_t;
	
	typedef struct packed unsigned {
		logic IQ_ERR;
		logic COM_ERR;
		logic DMOF;
		logic HW_FAIL;
		logic SYNC_ERR;
		logic DSIUV;
		logic DSIOV;
	} DSI_IRQ_STAT_t;
	
	typedef struct packed unsigned {
		logic IQ_ERR;
		logic COM_ERR;
		logic DMOF;
		logic HW_FAIL;
		logic SYNC_ERR;
		logic DSIUV;
		logic DSIOV;
	} DSI_IRQ_MASK_t;
	
	typedef struct packed unsigned {
		logic[3:0] CMD;
		logic[11:0] DATA;
	} DSI_CMD_t;
	
	typedef struct packed unsigned {
		logic[15:0] CRM_WORD2;
	} CRM_WORD2_t;
	
	typedef struct packed unsigned {
		logic[15:0] CRM_WORD1;
	} CRM_WORD1_t;
	
	typedef struct packed unsigned {
		logic[1:0] unused_1;
		logic SCE;
		logic CRC_ERR;
		logic TE;
		logic SYMBOL_ERROR;
		logic VDSI_ERR;
		logic CLK_ERR;
		logic[7:0] SYMBOL_COUNT;
	} PACKET_STAT_t;
	
	typedef struct packed unsigned {
		logic PC;
		logic[6:0] unused_1;
		logic[7:0] PACKET_COUNT;
	} FRAME_STAT_t;
	
	typedef struct packed unsigned {
		logic[14:0] TIME;
	} WAIT_TIME_t;
	
	typedef struct packed unsigned {
		logic PIN;
		logic[1:0] unused_1;
		logic[1:0] CHANNELS;
	} SYNC_t;
	
	typedef struct packed unsigned {
		logic[7:0] unused_1;
		logic[3:0] TRIM_REC2;
		logic[3:0] TRIM_REC1;
	} TRIM_DSI_REC_FALL_t;
	
	typedef struct packed unsigned {
		logic[7:0] unused_1;
		logic[3:0] TRIM_REC2;
		logic[3:0] TRIM_REC1;
	} TRIM_DSI_REC_RISE_t;
	
	typedef struct packed unsigned {
		logic[14:0] unused_1;
		logic PREVENT_DEACTIVATION;
	} TMR_DIG_DSI3_t;
	
	typedef struct packed unsigned {
		logic[10:0] unused_1;
		logic CMD_IGN;
		logic HW_FAIL;
		logic ALI_ERR;
		logic CRC_ERR;
		logic CMD_INC;
	} SPI_IRQ_STAT_t;
	
	typedef struct packed unsigned {
		logic[10:0] unused_1;
		logic CMD_IGN;
		logic HW_FAIL;
		logic ALI_ERR;
		logic CRC_ERR;
		logic CMD_INC;
	} SPI_IRQ_MASK_t;
	
	typedef struct packed unsigned {
		logic HE;
		logic BF;
		logic SCE;
		logic CRC;
		logic[1:0] NT;
		logic[5:0] unused_1;
		logic[1:0] PD;
		logic[1:0] CR;
	} STATUS_WORD_t;
	
	typedef struct packed unsigned {
		logic[11:0] VALID_COUNT;
	} BUF_VALID_COUNT_t;
	
	typedef struct packed unsigned {
		logic[15:0] FREE;
	} BUF_FREE_t;
	
	typedef struct packed unsigned {
		logic[15:0] READ_POINTER;
	} BUF_READ_POINTER_t;
	
	typedef struct packed unsigned {
		logic[15:0] WRITE_POINTER;
	} BUF_WRITE_POINTER_t;
	
	typedef struct packed unsigned {
		logic[15:0] VALID_POINTER;
	} BUF_VALID_POINTER_t;
	
	typedef struct packed unsigned {
		logic[8:0] unused_1;
		logic SPI_CMD_FE;
		logic[1:0] DSI_CMD_FE;
		logic[1:0] DSI_PDCM_FE;
		logic[1:0] DSI_CRM_FE;
	} BUF_IRQ_STAT_t;
	
	typedef struct packed unsigned {
		logic[8:0] unused_1;
		logic SPI_CMD_FE;
		logic[1:0] DSI_CMD_FE;
		logic[1:0] DSI_PDCM_FE;
		logic[1:0] DSI_CRM_FE;
	} BUF_IRQ_MASK_t;
	
	typedef struct packed unsigned {
		logic SPI_CMD_FW;
		logic[1:0] DSI_CMD_FW;
		logic[1:0] DSI_PDCM_FW;
		logic[1:0] DSI_CRM_FW;
	} BUF_FILL_WARN_t;
	
	typedef struct packed unsigned {
		logic[2:0] unused_1;
		logic HW_FAIL;
		logic RESERVED;
		logic ECC_FAIL;
		logic SUPPLY;
		logic[1:0] unused_2;
		logic[1:0] DSI;
		logic BUF;
		logic SPI;
		logic RESET;
		logic CLKREF;
		logic OTPFAIL;
	} IRQ_STAT_t;
	
	typedef struct packed unsigned {
		logic HW_FAIL;
		logic RESERVED;
		logic ECC_FAIL;
		logic SUPPLY;
		logic[1:0] unused_1;
		logic[1:0] DSI;
		logic BUF;
		logic SPI;
		logic RESET;
		logic CLKREF;
		logic OTPFAIL;
	} IRQ_MASK_t;
	
	typedef struct packed unsigned {
		logic RAM;
		logic SPI_DATA;
		logic SPI_CMD;
		logic SPI_CMD_BUF;
		logic[1:0] unused_1;
		logic[1:0] DSI_CMD;
		logic[1:0] DSI_TDMA;
		logic[1:0] DSI_CMD_BUF;
		logic[1:0] DSI_PDCM_DATA_BUF;
		logic[1:0] DSI_CRM_DATA_BUF;
	} ECC_IRQ_STAT_t;
	
	typedef struct packed unsigned {
		logic RAM;
		logic SPI_DATA;
		logic SPI_CMD;
		logic SPI_CMD_BUF;
		logic[1:0] unused_1;
		logic[1:0] DSI_CMD;
		logic[1:0] DSI_TDMA;
		logic[1:0] DSI_CMD_BUF;
		logic[1:0] DSI_PDCM_DATA_BUF;
		logic[1:0] DSI_CRM_DATA_BUF;
	} ECC_IRQ_MASK_t;
	
	typedef struct packed unsigned {
		logic RAM;
		logic SPI_DATA;
		logic SPI_CMD;
		logic SPI_CMD_BUF;
		logic[1:0] unused_1;
		logic[1:0] DSI_CMD;
		logic[1:0] DSI_TDMA;
		logic[1:0] DSI_CMD_BUF;
		logic[1:0] DSI_PDCM_DATA_BUF;
		logic[1:0] DSI_CRM_DATA_BUF;
	} ECC_CORR_IRQ_STAT_t;
	
	typedef struct packed unsigned {
		logic RAM;
		logic SPI_DATA;
		logic SPI_CMD;
		logic SPI_CMD_BUF;
		logic[1:0] unused_1;
		logic[1:0] DSI_CMD;
		logic[1:0] DSI_TDMA;
		logic[1:0] DSI_CMD_BUF;
		logic[1:0] DSI_PDCM_DATA_BUF;
		logic[1:0] DSI_CRM_DATA_BUF;
	} ECC_CORR_IRQ_MASK_t;
	
	typedef struct packed unsigned {
		logic[1:0] CLKREF_FREQ;
	} CLKREF_CONF_t;
	
	typedef struct packed unsigned {
		logic[15:0] CNT;
	} TB_CNT_t;
	
	typedef struct packed unsigned {
		logic[6:0] TRIM_OSC;
	} TRIM_OSC_t;
	
	typedef struct packed unsigned {
		logic[2:0] TCF;
	} TRIM_OSC_TCF_t;
	
	typedef struct packed unsigned {
		logic[11:0] address;
		logic[11:0] data;
		logic[7:0] unused_1;
	} OTP_WRITE_t;
	
	typedef struct packed unsigned {
		logic[11:0] address;
		logic[7:0] unused_1;
		logic[11:0] data;
	} OTP_READ_t;
	
	typedef struct packed unsigned {
		logic[3:0] unused_1;
		logic[11:0] ADDR;
	} OTP_READ_ADDRESS_t;
	
	typedef struct packed unsigned {
		logic[3:0] unused_1;
		logic[3:0] ECC;
		logic[7:0] VALUE;
	} OTP_READ_VALUE_t;
	
	typedef struct packed unsigned {
		logic[13:0] unused_1;
		logic[1:0] STATUS;
	} OTP_READ_STATUS_t;
	
	typedef struct packed unsigned {
		logic[3:0] unused_1;
		logic[11:0] PULSE_WIDTH;
	} OTP_WRITE_PULSE_WIDTH_t;
	
	typedef struct packed unsigned {
		logic unused_1;
		logic[5:0] ELIP_ECC;
		logic SRAM_ECC_SWAP;
		logic SRAM_ECC_SEL;
		logic[6:0] SRAM_ECC_VAL;
	} SRAM_ECC_CONTROL_t;
	

`endif
