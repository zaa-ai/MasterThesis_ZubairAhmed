//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef DSI3_MASTER_SEQUENCER_SV
`define DSI3_MASTER_SEQUENCER_SV

// You can insert code here by setting sequencer_inc_before_class in file dsi3_master.tpl

class dsi3_master_sequencer extends uvm_sequencer #(dsi3_master_tr);

	`uvm_component_utils(dsi3_master_sequencer)
	
	dsi3_master_config  m_config;

	function new(string name, uvm_component parent);
		super.new(name, parent);
	endfunction : new

	// You can insert code here by setting sequencer_inc_inside_class in file dsi3_master.tpl

endclass

typedef dsi3_master_sequencer dsi3_master_sequencer_t;

// You can insert code here by setting sequencer_inc_after_class in file dsi3_master.tpl

`endif

