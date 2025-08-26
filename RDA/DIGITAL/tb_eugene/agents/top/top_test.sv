//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------

`ifndef TOP_TEST_SV
`define TOP_TEST_SV

`include "includes/test_inc_before_class.sv"

class top_test extends uvm_test;

	`uvm_component_utils(top_test)

	top_env m_env;

	function new(string name, uvm_component parent);
		super.new(name, parent);
	endfunction

	// You can remove build_phase method by setting test_generate_methods_inside_class = no in file common.tpl
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		
		`include "includes/test_prepend_to_build_phase.sv"
	
		// You could modify any test-specific configuration object variables here
	
		// Include reg coverage from the register model
		uvm_reg::include_coverage("*", UVM_CVR_ALL);
	
		m_env = top_env::type_id::create("m_env", this);
		
		// You can insert code here by setting test_append_to_build_phase in file common.tpl
	
	endfunction

	`include "includes/test_inc_inside_class.sv"

endclass

// You can insert code here by setting test_inc_after_class in file common.tpl

`endif // TOP_TEST_SV

