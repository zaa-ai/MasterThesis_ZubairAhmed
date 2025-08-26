//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef ELIP_BUS_DRIVER_SV
`define ELIP_BUS_DRIVER_SV

// You can insert code here by setting driver_inc_before_class in file elip_bus.tpl

class elip_bus_driver extends uvm_driver #(elip_tr);

	`uvm_component_utils(elip_bus_driver)
	
	virtual	elip_bus_if vif;

  	elip_bus_config m_config;

  	function new(string name, uvm_component parent);
		super.new(name, parent);
	endfunction : new
	
	`include "includes/elip_driver_inc_inside_class.sv"
	
endclass

// You can insert code here by setting driver_inc_after_class in file elip_bus.tpl

`endif
