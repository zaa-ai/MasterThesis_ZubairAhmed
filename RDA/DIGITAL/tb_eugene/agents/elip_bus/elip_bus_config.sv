//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef ELIP_BUS_CONFIG_SV
`define ELIP_BUS_CONFIG_SV

// You can insert code here by setting agent_config_inc_before_class in file elip_bus.tpl

class elip_bus_config extends uvm_object;

	// Do not register config class with the factory
	
	virtual	elip_bus_if vif;
	
	uvm_active_passive_enum is_active = UVM_ACTIVE;
	bit	coverage_enable;       
	
	// You can insert variables here by setting config_var in file elip_bus.tpl
	
	// You can remove new by setting agent_config_generate_methods_inside_class = no in file elip_bus.tpl
	function new(string name = "");
		super.new("elip_bus_config");
	endfunction
	
	// You can insert code here by setting agent_config_inc_inside_class in file elip_bus.tpl

endclass 

// You can insert code here by setting agent_config_inc_after_class in file elip_bus.tpl

`endif
