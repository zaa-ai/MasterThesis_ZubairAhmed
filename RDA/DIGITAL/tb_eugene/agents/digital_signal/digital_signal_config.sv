//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef DIGITAL_SIGNAL_CONFIG_SV
`define DIGITAL_SIGNAL_CONFIG_SV

// You can insert code here by setting agent_config_inc_before_class in file digital_signal.tpl

class digital_signal_config extends uvm_object;

	// Do not register config class with the factory
	
	virtual	digital_signal_if vif;
	
	uvm_active_passive_enum is_active = UVM_ACTIVE;
	bit	coverage_enable;       
	
	logic initial_value	= 1'bx; // initial value to drive
	
	// You can remove new by setting agent_config_generate_methods_inside_class = no in file digital_signal.tpl
	function new(string name = "");
		super.new("digital_signal_config");
	endfunction
	
	// You can insert code here by setting agent_config_inc_inside_class in file digital_signal.tpl

endclass 

// You can insert code here by setting agent_config_inc_after_class in file digital_signal.tpl

`endif
