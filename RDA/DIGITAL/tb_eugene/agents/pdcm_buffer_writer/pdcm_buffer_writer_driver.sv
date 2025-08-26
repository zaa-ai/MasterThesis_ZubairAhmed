//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef PDCM_BUFFER_WRITER_DRIVER_SV
`define PDCM_BUFFER_WRITER_DRIVER_SV

// You can insert code here by setting driver_inc_before_class in file pdcm_buffer_writer.tpl

class pdcm_buffer_writer_driver extends uvm_driver #(pdcm_buffer_writer_tr);

	`uvm_component_utils(pdcm_buffer_writer_driver)
	
	virtual	pdcm_buffer_writer_if vif;

  	pdcm_buffer_writer_config m_config;

  	function new(string name, uvm_component parent);
		super.new(name, parent);
	endfunction : new
	
	`include "includes/pdcm_buffer_writer_driver_inc_inside_class.sv"
	
endclass

// You can insert code here by setting driver_inc_after_class in file pdcm_buffer_writer.tpl

`endif
