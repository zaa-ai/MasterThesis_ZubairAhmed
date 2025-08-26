//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef DSI3_MASTER_SEQ_ITEM_SV
`define DSI3_MASTER_SEQ_ITEM_SV

// You can insert code here by setting trans_inc_before_class in file dsi3_master.tpl

class dsi3_master_tr extends uvm_sequence_item; 

	`uvm_object_utils(dsi3_master_tr)

	// To include variables in copy, compare, print, record, pack, unpack, and compare2string, define them using trans_var in file dsi3_master.tpl
	// To exclude variables from compare, pack, and unpack methods, define them using trans_meta in file dsi3_master.tpl

	// Transaction variables
	rand logic data[$];
	rand dsi3_pkg::dsi3_msg_type msg_type;
	dsi3_pkg::dsi3_bit_time_e bit_time;
	
	constraint c0 {data.size() == msg_type;}

	function new(string name = "");
		super.new(name);
	endfunction	
	

	`include "includes/dsi3_master_trans_inc_inside_class.svh"

endclass

// You can insert code here by setting trans_inc_after_class in file dsi3_master.tpl

`endif // SPI_SEQ_ITEM_SV
