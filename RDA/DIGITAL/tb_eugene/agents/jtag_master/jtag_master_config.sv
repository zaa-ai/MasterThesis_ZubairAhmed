//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef JTAG_MASTER_CONFIG_SV
`define JTAG_MASTER_CONFIG_SV

// You can insert code here by setting agent_config_inc_before_class in file jtag_master.tpl

class jtag_master_config extends uvm_object;

	// Do not register config class with the factory
	
	virtual	jtag_master_if vif;
	
	uvm_active_passive_enum is_active = UVM_ACTIVE;
	bit	coverage_enable;       
	
	time cycle_time 			= 666ns;
	logic leading_level 		= 1'b1;
	bit[7:0] ir_length			= 8'd8;
	int dr_length 				= 32;
	int dr_length_elip_data	= 16;
	int dr_length_elip_addr	= 16;
	
	// You can remove new by setting agent_config_generate_methods_inside_class = no in file jtag_master.tpl
	function new(string name = "");
		super.new("jtag_master_config");
	endfunction
	
	// You can insert code here by setting agent_config_inc_inside_class in file jtag_master.tpl

endclass 

// You can insert code here by setting agent_config_inc_after_class in file jtag_master.tpl

`endif
