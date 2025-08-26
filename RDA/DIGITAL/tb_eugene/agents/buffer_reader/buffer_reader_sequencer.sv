//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef BUFFER_READER_SEQUENCER_SV
`define BUFFER_READER_SEQUENCER_SV

// You can insert code here by setting sequencer_inc_before_class in file buffer_reader.tpl

class buffer_reader_sequencer extends uvm_sequencer #(buffer_reader_tr);

	`uvm_component_utils(buffer_reader_sequencer)
	
	buffer_reader_config  m_config;

	function new(string name, uvm_component parent);
		super.new(name, parent);
	endfunction : new

	// You can insert code here by setting sequencer_inc_inside_class in file buffer_reader.tpl

endclass

typedef buffer_reader_sequencer buffer_reader_sequencer_t;

// You can insert code here by setting sequencer_inc_after_class in file buffer_reader.tpl

`endif

