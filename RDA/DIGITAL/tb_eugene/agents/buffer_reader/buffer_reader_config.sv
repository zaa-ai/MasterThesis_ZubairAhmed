//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef BUFFER_READER_CONFIG_SV
`define BUFFER_READER_CONFIG_SV

// You can insert code here by setting agent_config_inc_before_class in file buffer_reader.tpl

class buffer_reader_config extends uvm_object;

	// Do not register config class with the factory
	
	virtual	buffer_reader_if vif;
	
	uvm_active_passive_enum is_active = UVM_ACTIVE;
	bit	coverage_enable;       
	
	virtual clk_reset_if vif_clk_rst;
	
	// You can remove new by setting agent_config_generate_methods_inside_class = no in file buffer_reader.tpl
	function new(string name = "");
		super.new("buffer_reader_config");
	endfunction
	
	// You can insert code here by setting agent_config_inc_inside_class in file buffer_reader.tpl

endclass 

// You can insert code here by setting agent_config_inc_after_class in file buffer_reader.tpl

`endif
