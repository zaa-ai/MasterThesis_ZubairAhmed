//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef JTAG_MASTER_SEQ_ITEM_SV
`define JTAG_MASTER_SEQ_ITEM_SV

// You can insert code here by setting trans_inc_before_class in file jtag_master.tpl

class jtag_tr extends uvm_sequence_item; 

	`uvm_object_utils(jtag_tr)

	// To include variables in copy, compare, print, record, pack, unpack, and compare2string, define them using trans_var in file jtag_master.tpl
	// To exclude variables from compare, pack, and unpack methods, define them using trans_meta in file jtag_master.tpl

	// Transaction variables
	rand byte unsigned	ir_length;
	rand int unsigned	dr_length;
	rand int unsigned	ir_value;
	rand logic[265:0] 	dr_value;
	rand bit 			init_jtag;
	logic[265:0]		read_dr;
	int	unsigned		read_ir;
	constraint ir_length_co{ ir_length >= 0;}
	constraint ir_value_order_co{ solve ir_length before ir_value;}
	constraint ir_value_co{ ir_value inside { [0:(2**(ir_length+1))-1] };}
	constraint dr_order_co{solve ir_value before dr_length;}
	constraint dr_length_co{dr_length inside {[0:65535]};}
	constraint dr_value_order_co{ solve dr_length before dr_value;}
	constraint dr_value_co{dr_value inside{ [0:(2**(dr_length+1))-1]};}
	
	function new(string name = "");
		super.new(name);
	endfunction	
	

	`include "includes/jtag_trans_inc_inside_class.svh"

endclass

// You can insert code here by setting trans_inc_after_class in file jtag_master.tpl

`endif // SPI_SEQ_ITEM_SV
