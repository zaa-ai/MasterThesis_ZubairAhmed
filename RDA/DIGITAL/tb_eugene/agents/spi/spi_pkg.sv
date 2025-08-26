//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef SPI_PKG_SV
`define SPI_PKG_SV

package spi_pkg;

	`include "uvm_macros.svh"
	
	import uvm_pkg::*;
	
	import common_pkg::*;
	import common_env_pkg::*;
	
	`include "includes/spi_agent_inc_inside_package.svh"
	
	`include "spi_tr.sv"
	`include "spi_config.sv"
	`include "spi_driver.sv"
	`include "spi_monitor.sv"
	`include "spi_sequencer.sv"
	`include "spi_coverage.sv"
	`include "spi_agent.sv"
	`include "spi_seq_lib.sv"
	
	// You can insert code here by setting agent_inc_after_all_includes in file spi.tpl

endpackage

`endif // SPI_PKG_SV
