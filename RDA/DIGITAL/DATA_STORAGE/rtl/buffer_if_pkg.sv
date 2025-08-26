`ifndef BUFFER_IF_PKG
	`define BUFFER_IF_PKG
	/**
	 * Package: buffer_if_pkg
	 *
	 * packer for both buffer reader interface and buffer writer interface
	 */
	package buffer_if_pkg;
        typedef enum logic[3:0] {PDCM_IDLE_WRITE, PDCM_BUFFER_WRITE, PDCM_BUFFER_VALIDATE, PDCM_BUFFER_INVALIDATE, PDCM_BUFFER_CLEAR, PDCM_BUFFER_CLEAR_AND_INVALIDATE_NEXT, PDCM_BUFFER_WRITE_PACKET_HEADER, PDCM_BUFFER_WRITE_PACKET_HEADER_AGAIN, PDCM_BUFFER_WRITE_FRAME_HEADER, PDCM_BUFFER_WRITE_FRAME_HEADER_AGAIN} pdcm_buffer_writer_action_e;
		typedef	enum logic[2:0] {     IDLE_WRITE,      BUFFER_WRITE,      BUFFER_VALIDATE,      BUFFER_INVALIDATE,      BUFFER_CLEAR,      BUFFER_CLEAR_AND_INVALIDATE_NEXT, BUFFER_WRITE_FIRST} buffer_writer_action_e;
		typedef	enum logic[1:0] {IDLE_READ, BUFFER_MOVE_POINTER, BUFFER_READ} buffer_reader_action_e;
	endpackage
`endif
