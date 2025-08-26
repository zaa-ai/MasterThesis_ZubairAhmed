//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef DSI3_MASTER_CONFIG_SV
`define DSI3_MASTER_CONFIG_SV

// You can insert code here by setting agent_config_inc_before_class in file dsi3_master.tpl

class dsi3_master_config extends uvm_object;

	// Do not register config class with the factory
	
	virtual	dsi3_slave_if vif;
	
	uvm_active_passive_enum is_active = UVM_ACTIVE;
	bit	coverage_enable;       
	
	// You can insert variables here by setting config_var in file dsi3_master.tpl
	
	// Removed new by setting agent_config_generate_methods_inside_class = no in file dsi3_master.tpl
	
	`include "includes/dsi3_master_config_inc.svh"

endclass 

// You can insert code here by setting agent_config_inc_after_class in file dsi3_master.tpl

`endif
