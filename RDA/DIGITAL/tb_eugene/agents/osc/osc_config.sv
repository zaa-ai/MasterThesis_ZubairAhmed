//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef OSC_CONFIG_SV
`define OSC_CONFIG_SV

// You can insert code here by setting agent_config_inc_before_class in file osc.tpl

class osc_config extends uvm_object;

	// Do not register config class with the factory
	
	virtual	osc_if vif;
	
	uvm_active_passive_enum is_active = UVM_ACTIVE;
	bit	coverage_enable;       
	
	int	initial_frequency	= 500000; // initial value to drive -> 500kHz
	bit	initial_enabled		= 0; // initial value to drive -> enabled
	
	// You can remove new by setting agent_config_generate_methods_inside_class = no in file osc.tpl
	function new(string name = "");
		super.new("osc_config");
	endfunction
	
	// You can insert code here by setting agent_config_inc_inside_class in file osc.tpl

endclass 

// You can insert code here by setting agent_config_inc_after_class in file osc.tpl

`endif
