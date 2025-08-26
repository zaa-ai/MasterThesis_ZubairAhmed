//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef DIGITAL_SIGNAL_DRIVER_SV
`define DIGITAL_SIGNAL_DRIVER_SV

// You can insert code here by setting driver_inc_before_class in file digital_signal.tpl

class digital_signal_driver extends uvm_driver #(digital_signal_tr);

	`uvm_component_utils(digital_signal_driver)
	
	virtual	digital_signal_if vif;

  	digital_signal_config m_config;

  	function new(string name, uvm_component parent);
		super.new(name, parent);
	endfunction : new
	
	`include "includes/digital_signal_driver_inc_inside_class.sv"
	
endclass

// You can insert code here by setting driver_inc_after_class in file digital_signal.tpl

`endif
