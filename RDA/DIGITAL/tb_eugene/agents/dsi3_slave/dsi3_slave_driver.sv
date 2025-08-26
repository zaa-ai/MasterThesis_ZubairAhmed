//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef DSI3_SLAVE_DRIVER_SV
`define DSI3_SLAVE_DRIVER_SV

// You can insert code here by setting driver_inc_before_class in file dsi3_slave.tpl

class dsi3_slave_driver extends uvm_driver #(dsi3_slave_tr);

	`uvm_component_utils(dsi3_slave_driver)
	
	virtual	dsi3_slave_if vif;

  	dsi3_slave_config m_config;

  	function new(string name, uvm_component parent);
		super.new(name, parent);
	endfunction : new
	
	`include "includes/dsi3_slave_driver_inc_inside_class.sv"
	
endclass

// You can insert code here by setting driver_inc_after_class in file dsi3_slave.tpl

`endif
