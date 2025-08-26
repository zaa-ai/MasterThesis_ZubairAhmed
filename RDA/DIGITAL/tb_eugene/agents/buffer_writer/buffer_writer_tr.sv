//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef BUFFER_WRITER_SEQ_ITEM_SV
`define BUFFER_WRITER_SEQ_ITEM_SV

`include "includes/buffer_writer_trans_inc_before_class.sv"

class buffer_writer_tr extends uvm_sequence_item; 

	`uvm_object_utils(buffer_writer_tr)

	// To include variables in copy, compare, print, record, pack, unpack, and compare2string, define them using trans_var in file buffer_writer.tpl
	// To exclude variables from compare, pack, and unpack methods, define them using trans_meta in file buffer_writer.tpl

	// Transaction variables
	rand logic[15:0]	data;
	rand logic[5:0]		ecc;
	bit			full;
	bit			nearly_full;
	rand buffer_writer_action_e	action;
	
	function new(string name = "");
		super.new(name);
	endfunction	
	

	`include "includes/buffer_writer_trans_inc_inside_class.sv"

endclass

// You can insert code here by setting trans_inc_after_class in file buffer_writer.tpl

`endif // SPI_SEQ_ITEM_SV
