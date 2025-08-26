/**
 * Package: jtag_pkg
 * 
 * Definition of project specific JTAG constants and definitions
 */
package jtag_pkg;
	
	/*###   type definitions   ######################################################*/
	localparam C_DSR_WIDTH = 32;
	typedef logic [C_DSR_WIDTH-1:0] t_jtag_dsr;
	
	typedef enum logic[3:0] {TS_RESET, TS_RUN, 
		TS_SELECT_DR, TS_CAPTURE_DR, TS_SHIFT_DR, TS_EXIT1_DR, TS_EXIT2_DR, TS_PAUSE_DR, TS_UPDATE_DR,
		TS_SELECT_IR, TS_CAPTURE_IR, TS_SHIFT_IR, TS_EXIT1_IR, TS_EXIT2_IR, TS_PAUSE_IR, TS_UPDATE_IR} jtag_tap_states;
	
	typedef logic [7:0] t_jtag_isr;
	
	/*###   instructions   ######################################################*/
	/*
	manufacturer code always ("000" & x"45") = ASCII "E" !do not change!

	const logic [28:0]	C_IDCODE     = {digital_pkg::C_ID_PROJECT, jtag_id_pkg::C_ID_MANUFAKTURER};
	const logic [16:0]	C_ID_PROJECT = 17'd90212;
	 */
	localparam logic [11:0] 	C_ID_MANUFAKTURER = {3'b000, 8'h45, 1'b1};
	
	
	/*###   instructions   ######################################################*/
	localparam t_jtag_isr 	C_INSTR_BYPASS = 8'hff;
	localparam t_jtag_isr 	C_INSTR_IDCODE = 8'hfb;
	
	localparam t_jtag_isr 	C_INSTR_ATPG = 8'hb0;
	localparam t_jtag_isr 	C_INSTR_IDDQ = 8'hb1;
	localparam t_jtag_isr 	C_INSTR_SCAN_COMPRESSION = 8'hb8;

endpackage
