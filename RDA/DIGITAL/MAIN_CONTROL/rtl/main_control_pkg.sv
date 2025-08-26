`ifndef MAIN_CONTROL_PKG
	`define MAIN_CONTROL_PKG
	/**
	 * Package: main_control_pkg
	 *
	 * package for main control containing typedefs, parameters and structs
	 */
	package main_control_pkg;
		localparam	int OTP_ADDRESS_WIDTH = 12;
		localparam	int OTP_DATA_WIDTH = 12;
		typedef logic[OTP_ADDRESS_WIDTH-1:0] otp_address_t;
		typedef logic[OTP_DATA_WIDTH-1:0] otp_data_t;
		
		typedef enum logic[3:0] {
			RESET, RAM_ZEROING, WAIT_FOR_VCC_OK,
			WAIT_FOR_VRR_OK,
			READ_HIGH_ADDRESS, READ_LOW_ADDRESS,
			CHECK_ADDRESS,
			READ_HIGH_DATA, READ_LOW_DATA,
			PREPARE_WRITE_DATA, WRITE_DATA,
			WAITING_AFTER_TRIMMING, 
			WAIT_FOR_LDO_OK,
			POWERED_UP
		} main_state_t;
		
		typedef enum logic[1:0] {
			INITIAL = 2'b00,
			READING = 2'b01,
			FINISHED = 2'b10,
			FAIL = 2'b11
		} otp_read_out_status_e;
		
		localparam	int OTP_ECC_WIDTH_PER_WORD = 4;
		localparam	int OTP_DATA_WIDTH_PER_WORD = 8;
		
		typedef	logic[ OTP_ECC_WIDTH_PER_WORD-1:0] otp_word_ecc_t;
		typedef	logic[ OTP_DATA_WIDTH_PER_WORD-1:0] otp_word_data_t;
		
		typedef struct packed unsigned {
			otp_word_ecc_t	ecc;
			otp_word_data_t	data;
		}	otp_data_structure_t;
		
		localparam	int	OTP_CONTENT_WIDTH = 2*(OTP_ECC_WIDTH_PER_WORD + OTP_DATA_WIDTH_PER_WORD) + OTP_ADDRESS_WIDTH;
		localparam	int	OTP_CONTENT_DATA_WIDTH = 2*(OTP_DATA_WIDTH_PER_WORD) + OTP_ADDRESS_WIDTH;
		
		
		typedef struct packed unsigned {
			otp_word_data_t	high;
			otp_word_data_t	low;
		} 	otp_content_word_t;
		
		typedef struct packed unsigned {
			otp_address_t		address;
			otp_content_word_t	content;
		} 	otp_content_data_t;

		typedef struct packed unsigned {
			logic[3:0]	high;
			logic[3:0]	low;
		}	otp_content_ecc_t;
		
		typedef struct packed unsigned {
			otp_content_ecc_t	ecc;
			otp_content_data_t	data;
		}	otp_content_t;
		
	endpackage

`endif
