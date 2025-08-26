//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef OSC_SEQ_LIB_SV
`define OSC_SEQ_LIB_SV

class osc_default_seq extends uvm_sequence #(osc_tr);

	`uvm_object_utils(osc_default_seq)

	function new(string name = "");
		super.new(name);
	endfunction

	task body();
		`uvm_info(get_type_name(), "Default sequence starting", UVM_HIGH)
		
		req = osc_tr::type_id::create("req");
		start_item(req); 
		if ( !req.randomize() )
		  `uvm_error(get_type_name(), "Failed to randomize transaction")
		finish_item(req); 
		
		`uvm_info(get_type_name(), "Default sequence completed", UVM_HIGH)
	endtask

endclass

// You can insert code here by setting agent_seq_inc in file osc.tpl

`endif

