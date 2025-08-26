//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef DSI3_SLAVE_CONFIG_SV
`define DSI3_SLAVE_CONFIG_SV

// You can insert code here by setting agent_config_inc_before_class in file dsi3_slave.tpl

class dsi3_slave_config extends uvm_object;

	// Do not register config class with the factory
	
	virtual	dsi3_slave_if vif;
	
	uvm_active_passive_enum is_active = UVM_ACTIVE;
	bit	coverage_enable;       
	
	tdma_scheme pdcm_scheme;
	tdma_scheme crm_scheme;
	tdma_scheme dm_scheme;
	real chip_time_error = 0.0; // error injection: % of chip_time that may have a wrong current value
	protected timing_container rxd_timings;
	
	// Removed new by setting agent_config_generate_methods_inside_class = no in file dsi3_slave.tpl
	
	`include "includes/dsi3_slave_config_inc_inside_class.sv"

endclass 

// You can insert code here by setting agent_config_inc_after_class in file dsi3_slave.tpl

`endif
