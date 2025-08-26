//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef JTAG_MASTER_DRIVER_SV
`define JTAG_MASTER_DRIVER_SV

// You can insert code here by setting driver_inc_before_class in file jtag_master.tpl

class jtag_master_driver extends uvm_driver #(jtag_tr);

	`uvm_component_utils(jtag_master_driver)
	
	virtual	jtag_master_if vif;

  	jtag_master_config m_config;

  	function new(string name, uvm_component parent);
		super.new(name, parent);
	endfunction : new
	
	`include "includes/jtag_driver_inc_inside_class.sv"
	
endclass

// You can insert code here by setting driver_inc_after_class in file jtag_master.tpl

`endif
