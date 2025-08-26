//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef ELIP_BUS_SEQUENCER_SV
`define ELIP_BUS_SEQUENCER_SV

// You can insert code here by setting sequencer_inc_before_class in file elip_bus.tpl

class elip_bus_sequencer extends uvm_sequencer #(elip_tr);

	`uvm_component_utils(elip_bus_sequencer)
	
	elip_bus_config  m_config;

	function new(string name, uvm_component parent);
		super.new(name, parent);
	endfunction : new

	// You can insert code here by setting sequencer_inc_inside_class in file elip_bus.tpl

endclass

typedef elip_bus_sequencer elip_bus_sequencer_t;

// You can insert code here by setting sequencer_inc_after_class in file elip_bus.tpl

`endif

