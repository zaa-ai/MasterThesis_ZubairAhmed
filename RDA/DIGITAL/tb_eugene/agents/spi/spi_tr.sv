//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef SPI_SEQ_ITEM_SV
`define SPI_SEQ_ITEM_SV

`include "includes/spi_trans_inc_before_class.svh"

class spi_tr extends uvm_sequence_item; 

	`uvm_object_utils(spi_tr)

	// To include variables in copy, compare, print, record, pack, unpack, and compare2string, define them using trans_var in file spi.tpl
	// To exclude variables from compare, pack, and unpack methods, define them using trans_meta in file spi.tpl

	// Transaction variables
	rand logic[15:0] data_in;
	logic[15:0] data_out;
	int word_index;
	int bit_count;
	rand spi_tr_type tr_type;
	
	function new(string name = "");
		super.new(name);
	endfunction	
	

	`include "includes/spi_trans_inc_inside_class.svh"

endclass

// You can insert code here by setting trans_inc_after_class in file spi.tpl

`endif // SPI_SEQ_ITEM_SV
