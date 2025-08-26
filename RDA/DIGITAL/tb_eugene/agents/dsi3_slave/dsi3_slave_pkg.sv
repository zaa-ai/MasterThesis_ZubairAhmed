//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef DSI3_SLAVE_PKG_SV
`define DSI3_SLAVE_PKG_SV

package dsi3_slave_pkg;

	`include "uvm_macros.svh"
	
	import uvm_pkg::*;
	
	import common_pkg::*;
	import common_env_pkg::*;
	
	// You can insert code here by setting agent_inc_inside_package in file dsi3_slave.tpl
	
	`include "dsi3_slave_tr.sv"
	`include "dsi3_slave_config.sv"
	`include "dsi3_slave_driver.sv"
	`include "dsi3_slave_monitor.sv"
	`include "dsi3_slave_sequencer.sv"
	`include "dsi3_slave_coverage.sv"
	`include "dsi3_slave_agent.sv"
	`include "dsi3_slave_seq_lib.sv"
	
	// You can insert code here by setting agent_inc_after_all_includes in file dsi3_slave.tpl

endpackage

`endif // DSI3_SLAVE_PKG_SV
