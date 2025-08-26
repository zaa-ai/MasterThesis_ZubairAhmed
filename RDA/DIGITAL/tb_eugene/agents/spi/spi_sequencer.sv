//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef SPI_SEQUENCER_SV
`define SPI_SEQUENCER_SV

// You can insert code here by setting sequencer_inc_before_class in file spi.tpl

class spi_sequencer extends uvm_sequencer #(spi_tr);

	`uvm_component_utils(spi_sequencer)
	
	spi_config  m_config;

	function new(string name, uvm_component parent);
		super.new(name, parent);
	endfunction : new

	// You can insert code here by setting sequencer_inc_inside_class in file spi.tpl

endclass

typedef spi_sequencer spi_sequencer_t;

// You can insert code here by setting sequencer_inc_after_class in file spi.tpl

`endif

