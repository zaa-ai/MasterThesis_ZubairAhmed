
import digital_signal_pkg::*;

// CCC - command coding constants
typedef enum logic[3:0] {
	CMD_STATUS_READ         = 4'b0000,
	CMD_TX_CRC			   	= 4'b0001,
	CMD_REG_READ          	= 4'b0010,
	CMD_READ_CRM_PACKETS	= 4'b0011,
	CMD_READ_PDCM_PACKETS  	= 4'b0100,
	CMD_REG_WRITE         	= 4'b0101,
	CMD_DSI_CLEAR_QUEUE   	= 4'b0110,
	CMD_DSI_CLEAR_BUF     	= 4'b0111,
	CMD_CRM		   			= 4'b1000,
	CMD_MEASURE_CURRENT	  	= 4'b1001,
	CMD_DSI_DISCOVERY_MODE  = 4'b1010,
	CMD_UPLOAD_TDMA		   	= 4'b1011,
	CMD_PDCM			   	= 4'b1100,
	CMD_DSI_WAIT          	= 4'b1101,
	CMD_DSI_SYNC		   	= 4'b1110,
	CMD_RESET			   	= 4'b1111
} spi_cmd_type;

/*
 * SPI word MOSI -> MISO mirroring strategy
 */
typedef enum logic[1:0] {
	// all word of this command are mirrored
	ALL_WORDS,
	// only the first word of this command is mirrored
	COMMAND_WORD_ONLY,
	// noting is mirrored
	NONE
} spi_mirroring_type;

`include "data/flags_container.svh"
`include "spi_status_word.svh"
`include "sequences/spi_csb_handler.svh"
`include "sequences/spi_command.svh"
`include "components/tdma_scheme_upload_listener.svh" 