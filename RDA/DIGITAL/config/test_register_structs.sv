
`ifndef _TEST_REGISTER_STRUCTS
`define _TEST_REGISTER_STRUCTS

	typedef struct packed unsigned {
		logic[10:0] unused_1;
		logic VRR_2_ATB;
		logic VBG_2_ATB;
		logic VDDD_2_ATB;
		logic IC5U_2_ATB;
		logic IBP10U_2_ATB;
	} TMR_ANA_SUPPLY_t;
	
	typedef struct packed unsigned {
		logic[13:0] unused_1;
		logic DISCONNECT_TS;
		logic TS_2_ATB;
	} TMR_ANA_TEMP_SENSOR_t;
	
	typedef struct packed unsigned {
		logic[9:0] unused_1;
		logic OTP_VRR_LOAD;
		logic OTP_VPP_LOAD;
		logic OTP_VPP;
		logic OTP_VRR;
		logic OTP_VREF;
		logic OTP_VBG;
	} TMR_ANA_OTP_t;
	
	typedef struct packed unsigned {
		logic[14:0] unused_1;
		logic PREVENT_OVERTEMPERATURE_SWITCH_OFF;
	} TMR_DIG_SUPPLY_t;
	
	typedef struct packed unsigned {
		logic[14:0] unused_1;
		logic DAC;
	} TMR_SEL_WS_t;
	
	typedef struct packed unsigned {
		logic[10:0] unused_1;
		logic[4:0] DAC;
	} TMR_VAL_WS_t;
	
	typedef struct packed unsigned {
		logic[8:0] unused_1;
		logic IDAC_TX_CH1_2;
		logic VBN5V_DIV_CH1_2;
		logic INP_CH1_2;
		logic INN_CH1_2;
		logic VNG0_CH1_2;
		logic VNC0_CH1_2;
		logic VNC2_CH1_2;
	} TMR_ANA_DSI3_TX_t;
	
	typedef struct packed unsigned {
		logic[14:0] unused_1;
		logic I_Q_2_ATB;
	} TMR_ANA_DSI3_RX_t;
	
	typedef struct packed unsigned {
		logic[9:0] unused_1;
		logic unused_2;
		logic RX_ON;
		logic HVCASC_ON;
		logic TX_ON;
		logic RX_TXN;
		logic TX;
	} TMR_SEL_DSI3_t;
	
	typedef struct packed unsigned {
		logic[5:0] unused_1;
		logic[4:0] unused_2;
		logic RX_ON;
		logic HVCASC_ON;
		logic TX_ON;
		logic RX_TXN;
		logic TX;
	} TMR_VAL_DSI3_t;
	
	typedef struct packed unsigned {
		logic[12:0] unused_1;
		logic[2:0] tmr_in_tx;
	} TMR_IN_DSI3_t;
	
	typedef struct packed unsigned {
		logic[8:0] unused_1;
		logic PLL_VTUNE;
		logic PLL_VCTRL;
		logic PLL_PD_N;
		logic PLL_HiZ;
		logic PLL_UP;
		logic PLL_DOWN;
		logic PLL_IC5U;
	} TMR_ANA_TB_PLL_t;
	
	typedef struct packed unsigned {
		logic[12:0] unused_1;
		logic OSC_PREAMP;
		logic OSC_SFMAX;
		logic OSC_SFMIN;
	} TMR_ANA_TB_OSC_t;
	
	typedef struct packed unsigned {
		logic[12:0] unused_1;
		logic CLK_AUTO_TRIM_EN;
		logic CLKSW_TST_SEL;
		logic CLKSW_TST_EN;
	} TMR_DIG_TB_t;
	
	typedef struct packed unsigned {
		logic[13:0] unused_1;
		logic PLL_HOLD;
		logic PLL_ON;
	} TMR_VAL_TB_t;
	
	typedef struct packed unsigned {
		logic[13:0] unused_1;
		logic PLL_HOLD;
		logic PLL_ON;
	} TMR_SEL_TB_t;
	
	typedef struct packed unsigned {
		logic[2:0] unused_1;
		logic AUTOINC;
		logic[1:0] OTP_MON;
		logic CTRL_WE;
		logic CTRL_CLK;
		logic unused_2;
		logic SEL;
		logic unused_3;
		logic EN;
		logic unused_4;
		logic VPPEN;
		logic VRREN;
		logic EN_AUTO;
	} OTP_CONTROL_t;
	
	typedef struct packed unsigned {
		logic[7:0] OTP_MR;
		logic[15:0] OTP_MRR;
		logic[7:0] OTP_MPP;
	} OTP_CONFIG_t;
	
	typedef struct packed unsigned {
		logic unused_1;
		logic[2:0] MAX_SOAK;
		logic unused_2;
		logic SEL_MR;
		logic SEL_MRR;
		logic SEL_MPP;
		logic SEL_RD;
		logic SEL_TRP;
		logic STRESS;
		logic EN_SOAK;
		logic unused_3;
		logic SOAK;
		logic OTP_READ;
		logic OTP_PGM;
	} OTP_BIST_CONTROL_t;
	
	typedef struct packed unsigned {
		logic[1:0] ECCERR_H;
		logic[1:0] ECCERR_L;
		logic[1:0] unused_1;
		logic[1:0] RD_MODE;
		logic unused_2;
		logic[6:0] TRP;
	} OTP_READ_CONFIG_t;
	
	typedef struct packed unsigned {
		logic SOAK;
		logic FAIL1;
		logic FAIL0;
		logic BUSY;
		logic[3:0] SOAK_PULSE;
		logic DONE;
		logic unused_1;
		logic[5:0] PROG_BIT;
	} OTP_BIST_STATUS_t;
	
	typedef struct packed unsigned {
		logic[14:0] unused_1;
		logic ENABLE_ATB;
	} TMR_ANA_t;
	
	typedef struct packed unsigned {
		logic[12:0] unused_1;
		logic IGNORE_OSC_READY;
		logic SEL_SYNC;
		logic USE_JTAG;
	} TMR_DIG_t;
	
	typedef struct packed unsigned {
		logic[3:0] tmr_in_3;
		logic[3:0] tmr_in_2;
		logic[3:0] tmr_in_1;
		logic[3:0] tmr_in_0;
	} TMR_IN_t;
	
	typedef struct packed unsigned {
		logic EN_CSB;
		logic unused_1;
		logic[5:0] SEL_CSB;
		logic EN_SCK;
		logic unused_2;
		logic[5:0] SEL_SCK;
	} TMR_OUT_CSB_SCK_t;
	
	typedef struct packed unsigned {
		logic EN_MOSI;
		logic unused_1;
		logic[5:0] SEL_MOSI;
		logic EN_MISO;
		logic unused_2;
		logic[5:0] SEL_MISO;
	} TMR_OUT_MOSI_MISO_t;
	
	typedef struct packed unsigned {
		logic EN_BFWB;
		logic unused_1;
		logic[5:0] SEL_BFWB;
		logic EN_SYNCB;
		logic unused_2;
		logic[5:0] SEL_SYNCB;
	} TMR_OUT_BFWB_SYNCB_t;
	
	typedef struct packed unsigned {
		logic EN_DAB;
		logic unused_1;
		logic[5:0] SEL_DAB;
		logic EN_INTB;
		logic unused_2;
		logic[5:0] SEL_INTB;
	} TMR_OUT_DAB_INTB_t;
	
	typedef struct packed unsigned {
		logic[7:0] unused_1;
		logic EN_RFC;
		logic unused_2;
		logic[5:0] SEL_RFC;
	} TMR_OUT_RFC_t;
	
	typedef struct packed unsigned {
		logic[3:0] unused_1;
		logic[15:0] PROJECT;
		logic[10:0] MANUFACTURER;
		logic unused_2;
	} JTAG_ID_t;
	
	typedef struct packed unsigned {
		logic unused_1;
	} JTAG_BYPASS_t;
	
	typedef struct packed unsigned {
		logic[9:0] unused_1;
		logic DISABLE_OSC;
		logic VDD_DIS;
		logic VDD_ILOAD_DIS;
		logic COMPRESSION;
		logic VDD_RDIV_DIS;
		logic SCAN;
	} SCAN_t;
	
	typedef struct packed unsigned {
		logic[12:0] unused_1;
		logic FOUR_6N;
		logic BITWISE;
		logic EN;
	} SRAM_BIST_CTRL_t;
	
	typedef struct packed unsigned {
		logic[13:0] unused_1;
		logic[1:0] STATUS;
	} SRAM_BIST_STAT_t;
	
	typedef struct packed unsigned {
		logic[15:0] ADDR;
		logic[15:0] DATA;
	} IR_ELIP_RDF_t;
	
	typedef struct packed unsigned {
		logic[15:0] DATA;
	} IR_ELIP_RD_t;
	
	typedef struct packed unsigned {
		logic[15:0] DATA;
	} IR_ELIP_RDI_t;
	
	typedef struct packed unsigned {
		logic[15:0] ADDR;
		logic[15:0] DATA;
	} IR_ELIP_WRF_t;
	
	typedef struct packed unsigned {
		logic[15:0] DATA;
	} IR_ELIP_WR_t;
	
	typedef struct packed unsigned {
		logic[15:0] unused_1;
	} IR_ELIP_WRI_t;
	

`endif
