`ifndef SPI_IMPLEMENTATION_PKG
`define SPI_IMPLEMENTATION_PKG
/*------------------------------------------------------------------------------
 * Project       : p52144
 * Author        : jvoi
 * Creation date : Jan 16, 2023
 * Description   : Package for SPI implementation constants, typedefs and functions
 *------------------------------------------------------------------------------*/
package spi_implementation_pkg;
	import project_pkg::*;
	
	parameter int unsigned shift_length = 16;
	parameter int shift_length_width = 4;
	parameter logic[15:0] crc_ccitt_16_polynom = 16'b0001_0000_0010_0001;
	parameter data_t CRC_RESET = 16'h84cf;
	
	typedef logic [shift_length-1:0] shift_register_t;
	typedef logic [shift_length_width-1:0] shift_register_counter_t;
	
	function automatic logic[15:0] crc_ccitt_16_word(input logic[15:0] crc_initial, input logic[15:0] data);
        logic[15:0] crc;
        crc = crc_initial;
		for (int k=15; k>=0; k--) begin
			crc = {crc[14:0], data[k]} ^ ({16{crc[15]}} & crc_ccitt_16_polynom);
		end
		return crc;
	endfunction
	
	typedef enum logic[3:0]{
		NO_COMMAND,
		CHECK_MOSI_CRC, 
		WRITE_COMMAND, WAIT_FOR_NEXT_WORD,
		READ_REGISTER, READ_NEXT_REGISTER,
		VALIDATE_BUFFER, INVALIDATE_BUFFER,
		GET_CHANNELS_FOR_PACKET_READING,
		READ_CRM_CHANNEL, READ_CRM_DATA, READ_CRM_FINISH,
		READ_PDCM_CHANNEL, READ_PDCM_FRAME, READ_PDCM_FINISH
	} spi_command_state_e;
	
	typedef logic[5:0] word_count_t;
	typedef logic[1:0] packet_count_t;
	
	typedef struct {
		dsi_logic_t    channels;
	} packet_read_command_info_t;
	
	typedef enum logic [1:0] {PACKET_ONGOING, PACKET_FINISHED, PACKET_FILL_ZERO, PACKET_READ_REST} packet_state_e;
	
	// command coding
	typedef enum logic[3:0] {
		IC_STATUS = 4'h0,
        CRC_OUT = 4'h1,
		RESET = 4'hf,

		// Command queue commands
		REG_WRITE = 4'h5,
		CLEAR_COMMAND_QUEUE = 4'h6,
		CLEAR_DSI_BUFFERS = 4'h7,

		// DSI commands
		DSI_CRM = 4'h8,
		DSI_ILOAD = 4'h9,
		DSI_START_DISCOVERY = 4'ha,
		DSI_UPLOAD_TDMA = 4'hb,
		DSI_PDCM = 4'hc,
		DSI_WAIT = 4'hd,
		SYNC = 4'he,

		// READ commands
		REG_READ = 4'h2,
		DSI_READ_CRM_DATA = 4'h3,
		DSI_READ_PDCM_DATA = 4'h4
		//		DSI_READ_BUFFER = 4'hb
	} spi_command_e;

	typedef struct packed {
		spi_command_e 	command;
		logic [11:0]	data;
	} spi_command_t;

	parameter	int	TDMA_PACKET_OR_VALIDATE_SELECT = 5;
	typedef enum logic {VALIDATE_SCHEME = 1'b0, UPLOAD_PACKET = 1'b1} tdma_sector_t;
    
    typedef enum logic[1:0] {NONE, READ_FRAME_INFO, READ_PACKET_INFO} tdma_read_action_t;
	
	// @SuppressProblem -type partially_unread_data -count 1 -length 1
	function automatic int get_command_length(spi_command_t command);
		case (command.command)
			DSI_READ_PDCM_DATA, DSI_READ_CRM_DATA: return 0;
			CRC_OUT, CLEAR_COMMAND_QUEUE, CLEAR_DSI_BUFFERS, DSI_PDCM, SYNC, DSI_START_DISCOVERY, DSI_ILOAD: return 1;
			REG_WRITE, DSI_WAIT, REG_READ: return 2;
			DSI_CRM: return 3;
			DSI_UPLOAD_TDMA: begin
				if (command[TDMA_PACKET_OR_VALIDATE_SELECT] == UPLOAD_PACKET) return 4;
				else					return 2;
            end
            IC_STATUS: return 0;
		endcase
    endfunction
    
    parameter   data_t  SPI_RESET_COMMAND_WORD = 16'hffff;
	
	parameter	int MSB_CHANNEL_SELECT = 11;
	parameter	int LSB_CHANNEL_SELECT = 10;
	
	parameter	int BIT_NO_RESPONSE = 0;
	parameter	int BIT_EXTERNAL_SYNC = 0;
	parameter	int MSB_PDCM_PERIODS = 7;
	parameter	int LSB_PDCM_PERIODS = 0;
	
	parameter	int MSB_TDMA_PACKET_COUNT = 3;
	parameter	int LSB_TDMA_PACKET_COUNT = 0;
	parameter	int MSB_TDMA_PACKET_SYMBOL_COUNT = 7;
	parameter	int LSB_TDMA_PACKET_SYMBOL_COUNT = 0;
    
    parameter   int BIT_CLEAR_DSI_BUFFERS_PD = 1;
    parameter   int BIT_CLEAR_DSI_BUFFERS_CR = 0;
	
endpackage
`endif