//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef JTAG_MASTER_MONITOR_SV
`define JTAG_MASTER_MONITOR_SV

class jtag_master_monitor extends uvm_monitor;

	`uvm_component_utils(jtag_master_monitor)
	
	virtual	jtag_master_if vif;

  	jtag_master_config m_config;

  	uvm_analysis_port #(jtag_tr) analysis_port;

  	jtag_tr m_trans;

  	function new(string name, uvm_component parent);
  		super.new(name, parent);
  		analysis_port = new("analysis_port", this);
	endfunction
		
	
	// You can insert code here by setting monitor_inc_inside_class in file jtag_master.tpl
	
endclass

// You can insert code here by setting monitor_inc_after_class in file jtag_master.tpl

`endif
