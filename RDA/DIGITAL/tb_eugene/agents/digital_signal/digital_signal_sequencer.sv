//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef DIGITAL_SIGNAL_SEQUENCER_SV
`define DIGITAL_SIGNAL_SEQUENCER_SV

// You can insert code here by setting sequencer_inc_before_class in file digital_signal.tpl

class digital_signal_sequencer extends uvm_sequencer #(digital_signal_tr);

	`uvm_component_utils(digital_signal_sequencer)
	
	digital_signal_config  m_config;

	function new(string name, uvm_component parent);
		super.new(name, parent);
	endfunction : new

	// You can insert code here by setting sequencer_inc_inside_class in file digital_signal.tpl

endclass

typedef digital_signal_sequencer digital_signal_sequencer_t;

// You can insert code here by setting sequencer_inc_after_class in file digital_signal.tpl

`endif

