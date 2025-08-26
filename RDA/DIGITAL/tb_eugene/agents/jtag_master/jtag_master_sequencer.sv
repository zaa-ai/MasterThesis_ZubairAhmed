//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef JTAG_MASTER_SEQUENCER_SV
`define JTAG_MASTER_SEQUENCER_SV

// You can insert code here by setting sequencer_inc_before_class in file jtag_master.tpl

class jtag_master_sequencer extends uvm_sequencer #(jtag_tr);

	`uvm_component_utils(jtag_master_sequencer)
	
	jtag_master_config  m_config;

	function new(string name, uvm_component parent);
		super.new(name, parent);
	endfunction : new

	// You can insert code here by setting sequencer_inc_inside_class in file jtag_master.tpl

endclass

typedef jtag_master_sequencer jtag_master_sequencer_t;

// You can insert code here by setting sequencer_inc_after_class in file jtag_master.tpl

`endif

