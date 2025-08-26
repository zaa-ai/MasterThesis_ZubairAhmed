//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef SPI_CONFIG_SV
`define SPI_CONFIG_SV

// You can insert code here by setting agent_config_inc_before_class in file spi.tpl

class spi_config extends uvm_object;

	// Do not register config class with the factory
	
	virtual	spi_if vif;
	
	uvm_active_passive_enum is_active = UVM_ACTIVE;
	bit	coverage_enable;       
	
	time cycle_time 				= 1000ns;	// Bit time
	bit csn_polarity				= 1'b0; 	// 0: active low					1: active high
	bit sck_polarity				= 1'b0; 	// 0: inactive low					1: inactive high
	bit sck_phase					= 1'b1; 	// 0: first sample then shift		1: first shift then sample
	logic sck_init_value			= 1'b0; 	// intial value of sck
	time csn_to_sck				= 1000ns;	// Time from activation of CSN to first SCK edge
	time sck_to_csn				= 1000ns;	// Time from last SCK edge to deactivation of CSN
	time inter_word_gap			= 0us;      // Time between 2 successive SPI words
	spi_csb_handler csb_handler	= per_word_csb_hander::create();
	
	// You can remove new by setting agent_config_generate_methods_inside_class = no in file spi.tpl
	function new(string name = "");
		super.new("spi_config");
	endfunction
	
	// You can insert code here by setting agent_config_inc_inside_class in file spi.tpl

endclass 

// You can insert code here by setting agent_config_inc_after_class in file spi.tpl

`endif
