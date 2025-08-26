//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef BUFFER_READER_PKG_SV
`define BUFFER_READER_PKG_SV

package buffer_reader_pkg;

	`include "uvm_macros.svh"
	
	import uvm_pkg::*;
	
	import common_pkg::*;
	import common_env_pkg::*;
	
	// You can insert code here by setting agent_inc_inside_package in file buffer_reader.tpl
	
	`include "buffer_reader_tr.sv"
	`include "buffer_reader_config.sv"
	`include "buffer_reader_driver.sv"
	`include "buffer_reader_monitor.sv"
	`include "buffer_reader_sequencer.sv"
	`include "buffer_reader_coverage.sv"
	`include "buffer_reader_agent.sv"
	`include "buffer_reader_seq_lib.sv"
	
	// You can insert code here by setting agent_inc_after_all_includes in file buffer_reader.tpl

endpackage

`endif // BUFFER_READER_PKG_SV
