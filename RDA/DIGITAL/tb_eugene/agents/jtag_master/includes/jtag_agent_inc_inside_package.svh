
/************ Sidense SLP OTP *****************
 * 0xA0 : c_instr_OTP_CTRL 
 * 0xA1 : c_instr_OTP_CONF
 * 0xA2 : c_instr_otp_write
 * 0xA3 : c_instr_otp_write_ecc
 * 0xA4 : c_instr_otp_read 
 * 0xA5 : c_instr_otp_read_ecc
 * 0xA6 : c_instr_otpbist_ctrl
 * 0xA7 : c_instr_otpbist_conf
 * 0xA8 : c_instr_otpbist_stat
 ***************************************/
const int OTP_CTRL						= 'ha0;
const int OTP_CONF						= 'ha1;
const int OTP_WRITE						= 'ha2;
const int OTP_WRITE_ECC					= 'ha3;
const int OTP_READ						= 'ha4;
const int OTP_READ_ECC					= 'ha5;
const int OTP_BIST_CTRL					= 'ha6;
const int OTP_BIST_CONF					= 'ha7;
const int OTP_BIST_STAT					= 'ha8;

const int ELIP_RDF		= 'hC0; // full read access
const int ELIP_RD		= 'hC1; // read again (same address)
const int ELIP_RDI		= 'hC2; // read @ incremented address
const int ELIP_WRF		= 'hC3; // full write access  
const int ELIP_WR		= 'hC4; // write again (same address)
const int ELIP_WRI		= 'hC5; // write @ incremented address

// look up table for streaming extension
const string jtag_instructions [int]='{

		'hFF:"JTAG_STD_BYPASS", 	// BYPASS
		'hFE:"JTAG_STD_EXTEST", 	// EXTEST 
		'hFD:"JTAG_STD_PRELOAD", 	// PRELOAD(/SAMPLE)
		'hFC:"JTAG_STD_SAMPLE", 	// SAMPLE

		'hB0:"JTAG_ATPG",
		'hB1:"JTAG_IDDQ",			//Enter IDDQ-Mode
		'hB8:"JTAG_ATPG_COMP",
		'hB9:"JTAG_IDDQ_COMP",
		
		'hB2:"JTAG_CLK_CTRL",
		'hB3:"JTAG_TCK_CTRL",
		'hB5:"JTAG_CLK_CTRL_ASYNC",
		'hB6:"JTAG_TCK_CTRL_ASYNC",
		'hB5:"JTAG_CLK2TDO",
		
		'he5:"JTAG_RST_CTRL",
		
		'hC6:"JTAG_IR_TMR_ANA_1",			
		'hC7:"JTAG_IR_TMR_ANA_2", 			
		'hC9:"JTAG_IR_TMR_DIG",    		
		'hCA:"JTAG_IR_TMR_DIG_OUT_SPI", 	
		'hCB:"JTAG_IR_TMR_DIG_OUT_GPIO", 	
		'hCC:"JTAG_IR_TMR_DIG_SEL", 		
		'hCD:"JTAG_IR_TMR_DIG_VAL", 		
		'hCD:"JTAG_IR_TMR_DIG_IN",  		

		// Sidense OTP
		'ha0: "OTP_CTRL",
		'ha1: "OTP_CONF",
		'ha2: "OTP_WRITE",
		'ha3: "OTP_WRITE_ECC",
		'ha4: "OTP_READ",
		'ha5: "OTP_READ_ECC",
		'ha6: "OTP_BIST_CTRL",
		'ha7: "OTP_BIST_CONF",
		'ha8: "OTP_BIST_STAT",
		 
		'hC0:"ELIP_RDF", 	// full read access
		'hC1:"ELIP_RD", 	// read again (same address)
		'hC2:"ELIP_RDI", 	// read @ incremented address
		'hC3:"ELIP_WRF", 	// full write access  
		'hC4:"ELIP_WR", 	// write again (same address)
		'hC5:"ELIP_WRI", 	// write @ incremented address
		'hEE:"DEBUG_MODE" 	// jtag debug mode access
	};	