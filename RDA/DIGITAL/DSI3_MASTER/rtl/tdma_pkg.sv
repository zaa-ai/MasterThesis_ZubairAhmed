/*------------------------------------------------------------------------------
 * File          : tdma_pkg.sv
 * Project       : p52144
 * Author        : jvoi
 * Creation date : Jan 26, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

package tdma_pkg;
	
	import project_pkg::*;
	
	typedef enum logic {
		HEADER,
		PACKET
	} tdma_target_t;
	
	typedef enum logic[1:0] {
		NO_ACTION,
		WRITE_PACKET,
		WRITE_HEADER,
		VALIDATE
	} tdma_writer_action_t;
    
	typedef enum logic[1:0] {
		NO_READ_ACTION,
		READ_NEXT_PACKET,
		INITIALIZE
	} tdma_reader_action_t;
    
	typedef enum logic[1:0] {
		NO_SPI_READ_ACTION,
		READ_PACKET_COUNT,
        READ_SYMBOL_COUNT_OF_PACKET
	} tdma_spi_reader_action_t;
	
    typedef struct packed {
        logic[11:0] unused;
        logic[ 3:0] packet_count;
        ecc_t       ecc;
    } tdma_header_packet_count_ecc_t;
	
    typedef struct packed {
        logic[11:0] unused;
        logic[ 3:0] packet_count;
    } tdma_header_packet_count_t;
    
	typedef struct packed {
        tdma_header_packet_count_ecc_t	packet_count;
		data_ecc_t	period;
	} tdma_header_ecc_t;
    
	typedef struct packed {
        tdma_header_packet_count_t	packet_count;
		data_t	period;
	} tdma_header_t;
	
	typedef struct packed {
		logic[1:0]	id_config;
		logic[5:0]	unused;
		logic[7:0]	symbol_count; //TODO: check, if this may come from spi_implematation_pkg
	} tdma_packet_info_data_t;
	
	typedef struct packed {
        tdma_packet_info_data_t data;
        ecc_t                   ecc;
	} tdma_packet_info_t;
	
	typedef struct packed {
		data_ecc_t	earliest;
		data_ecc_t	latest;
        tdma_packet_info_t	info; 
	} tdma_packet_ecc_t;
    
	typedef struct packed {
		data_t	earliest;
		data_t	latest;
        tdma_packet_info_data_t	info; 
	} tdma_packet_t;
	
	typedef struct packed {
		logic[11:0] unused;
		logic[ 3:0] packet_count;
	} tdma_header_info_t;
	
	typedef logic[3:0] tdma_packet_index_t;
	
	typedef enum logic [2:0] {
		IDLE,
		HEADER1,
		HEADER2,
		PACKET_EARLIEST,
		PACKET_LATEST,
		PACKET_INFO,
		ACKNOWLEDGE
	} tmda_buffer_state_t;
	
	typedef	enum logic[2:0] {S_IDLE, S_VALIDATE, S_WRITE_PACKET, S_WRITE_HEADER, S_READ_HEADER, S_INITIALIZE, S_READ_FIRST_PACKET, S_READ_NEXT_PACKET} tdma_manager_state_t;
	
	typedef struct packed {
		tdma_packet_ecc_t	current_packet;
		tdma_packet_ecc_t	next_packet;
		tdma_header_ecc_t	header;
	} tdma_information_package_ecc_t;
    
    typedef struct packed {
        tdma_packet_t   current_packet;
        tdma_packet_t   next_packet;
        tdma_header_t   header;
    } tdma_information_package_t;
    
	parameter tdma_packet_ecc_t	EMPTY_TDMA_PACKET = '{EMPTY_DATA, EMPTY_DATA, EMPTY_DATA};
	parameter tdma_header_ecc_t	EMPTY_TDMA_HEADER = '{{12'd0, 4'd0, ECC_FOR_DATA_0}, EMPTY_DATA};
	
endpackage : tdma_pkg