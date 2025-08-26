//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef OSC_DRIVER_SV
`define OSC_DRIVER_SV

// You can insert code here by setting driver_inc_before_class in file osc.tpl

class osc_driver extends uvm_driver #(osc_tr);

	`uvm_component_utils(osc_driver)
	
	virtual	osc_if vif;

  	osc_config m_config;

  	function new(string name, uvm_component parent);
		super.new(name, parent);
	endfunction : new
	
	`include "includes/osc_driver_inc_inside_class.sv"
	
endclass

// You can insert code here by setting driver_inc_after_class in file osc.tpl

`endif
