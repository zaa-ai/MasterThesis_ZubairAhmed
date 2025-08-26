//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef PDCM_BUFFER_WRITER_CONFIG_SV
`define PDCM_BUFFER_WRITER_CONFIG_SV

// You can insert code here by setting agent_config_inc_before_class in file pdcm_buffer_writer.tpl

class pdcm_buffer_writer_config extends uvm_object;

	// Do not register config class with the factory
	
	virtual	pdcm_buffer_writer_if vif;
	
	uvm_active_passive_enum is_active = UVM_ACTIVE;
	bit	coverage_enable;       
	
	virtual clk_reset_if vif_clk_rst;
	bit is_completly_passive = 1'b0;
	
	// You can remove new by setting agent_config_generate_methods_inside_class = no in file pdcm_buffer_writer.tpl
	function new(string name = "");
		super.new("pdcm_buffer_writer_config");
	endfunction
	
	// You can insert code here by setting agent_config_inc_inside_class in file pdcm_buffer_writer.tpl

endclass 

// You can insert code here by setting agent_config_inc_after_class in file pdcm_buffer_writer.tpl

`endif
