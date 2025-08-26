//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef DSI3_SLAVE_SEQ_ITEM_SV
`define DSI3_SLAVE_SEQ_ITEM_SV

`include "includes/dsi3_slave_trans_inc_before_class.sv"

class dsi3_slave_tr extends uvm_sequence_item; 

	`uvm_object_utils(dsi3_slave_tr)

	// To include variables in copy, compare, print, record, pack, unpack, and compare2string, define them using trans_var in file dsi3_slave.tpl
	// To exclude variables from compare, pack, and unpack methods, define them using trans_meta in file dsi3_slave.tpl

	// Transaction variables
	rand logic[3:0]		data [$];
	rand int			tolerance_int; // 1000 => 100% => 0% tolerance
	rand int			chiptime;
	rand int			chips_per_symbol; // can be used to create single/double chip disturbances
	bit					symbol_coding_error;
	rand dsi3_pkg::dsi3_msg_type	msg_type;
	rand error_injection_e	symbol_coding_error_injection;
	rand error_injection_e	chip_length_error_injection;
	real tolerance;
	
	constraint c0 {tolerance_int inside {[900:1100]};}

	constraint c1 {data.size() inside {[1:2048]};}

	constraint c2 {msg_type inside {dsi3_pkg::DM, dsi3_pkg::CRM, dsi3_pkg::PDCM};}

	constraint c3 {chiptime inside {[2:10]};}

	constraint c4 {chips_per_symbol inside {[1:3]};}

	function new(string name = "");
		super.new(name);
	endfunction	
	

	`include "includes/dsi3_slave_trans_inc_inside_class.sv"

endclass

// You can insert code here by setting trans_inc_after_class in file dsi3_slave.tpl

`endif // SPI_SEQ_ITEM_SV
