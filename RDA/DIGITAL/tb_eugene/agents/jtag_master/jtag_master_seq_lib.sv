//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef JTAG_MASTER_SEQ_LIB_SV
`define JTAG_MASTER_SEQ_LIB_SV

class jtag_master_default_seq extends uvm_sequence #(jtag_tr);

	`uvm_object_utils(jtag_master_default_seq)

	function new(string name = "");
		super.new(name);
	endfunction

	task body();
		`uvm_info(get_type_name(), "Default sequence starting", UVM_HIGH)
		
		req = jtag_tr::type_id::create("req");
		start_item(req); 
		if ( !req.randomize() )
		  `uvm_error(get_type_name(), "Failed to randomize transaction")
		finish_item(req); 
		
		`uvm_info(get_type_name(), "Default sequence completed", UVM_HIGH)
	endtask

endclass

`include "includes/jtag_seq_inc.sv"

`endif

