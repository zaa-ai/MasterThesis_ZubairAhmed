//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef REAL_SIGNAL_MONITOR_SV
`define REAL_SIGNAL_MONITOR_SV

class real_signal_monitor extends uvm_monitor;

	`uvm_component_utils(real_signal_monitor)
	
	virtual	real_signal_if vif;

  	real_signal_config m_config;

  	uvm_analysis_port #(real_signal_tr) analysis_port;

  	real_signal_tr m_trans;

  	function new(string name, uvm_component parent);
  		super.new(name, parent);
  		analysis_port = new("analysis_port", this);
	endfunction
		
	
	// You can insert code here by setting monitor_inc_inside_class in file real_signal.tpl
	
endclass

// You can insert code here by setting monitor_inc_after_class in file real_signal.tpl

`endif
