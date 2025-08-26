//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef BUFFER_WRITER_PKG_SV
`define BUFFER_WRITER_PKG_SV

package buffer_writer_pkg;

	`include "uvm_macros.svh"
	
	import uvm_pkg::*;
	
	import common_pkg::*;
	import common_env_pkg::*;
	
	// You can insert code here by setting agent_inc_inside_package in file buffer_writer.tpl
	
	`include "buffer_writer_tr.sv"
	`include "buffer_writer_config.sv"
	`include "buffer_writer_driver.sv"
	`include "buffer_writer_monitor.sv"
	`include "buffer_writer_sequencer.sv"
	`include "buffer_writer_coverage.sv"
	`include "buffer_writer_agent.sv"
	`include "buffer_writer_seq_lib.sv"
	
	// You can insert code here by setting agent_inc_after_all_includes in file buffer_writer.tpl

endpackage

`endif // BUFFER_WRITER_PKG_SV
