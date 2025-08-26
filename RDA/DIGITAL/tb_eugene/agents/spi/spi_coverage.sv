//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef SPI_COVERAGE_SV
`define SPI_COVERAGE_SV

// You can insert code here by setting agent_cover_inc_before_class in file spi.tpl

class spi_coverage extends uvm_subscriber #(spi_tr);

	`uvm_component_utils(spi_coverage)
	
	spi_config m_config;
	
	
	function new(string name, uvm_component parent);
		super.new(name, parent);
	endfunction
	
	function void write(input spi_tr t);
	endfunction
	
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		if (!uvm_config_db #(spi_config)::get(this, "", "config", m_config)) begin
			`uvm_error(get_type_name(), "spi config not found")
		end
	endfunction
	
	function void report_phase(uvm_phase phase);
	endfunction
	
	// You can insert code here by setting agent_cover_inc_inside_class in file spi.tpl

endclass 

// You can insert code here by setting agent_cover_inc_after_class in file spi.tpl

`endif

