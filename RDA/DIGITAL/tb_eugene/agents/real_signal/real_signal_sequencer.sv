//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef REAL_SIGNAL_SEQUENCER_SV
`define REAL_SIGNAL_SEQUENCER_SV

// You can insert code here by setting sequencer_inc_before_class in file real_signal.tpl

class real_signal_sequencer extends uvm_sequencer #(real_signal_tr);

	`uvm_component_utils(real_signal_sequencer)
	
	real_signal_config  m_config;

	function new(string name, uvm_component parent);
		super.new(name, parent);
	endfunction : new

	// You can insert code here by setting sequencer_inc_inside_class in file real_signal.tpl

endclass

typedef real_signal_sequencer real_signal_sequencer_t;

// You can insert code here by setting sequencer_inc_after_class in file real_signal.tpl

`endif

