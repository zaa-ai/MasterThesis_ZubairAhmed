//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef SPI_DRIVER_SV
`define SPI_DRIVER_SV

// You can insert code here by setting driver_inc_before_class in file spi.tpl

class spi_driver extends uvm_driver #(spi_tr);

	`uvm_component_utils(spi_driver)
	
	virtual	spi_if vif;

  	spi_config m_config;

  	function new(string name, uvm_component parent);
		super.new(name, parent);
	endfunction : new
	
	`include "includes/spi_driver_inc_inside_class.sv"
	
endclass

// You can insert code here by setting driver_inc_after_class in file spi.tpl

`endif
