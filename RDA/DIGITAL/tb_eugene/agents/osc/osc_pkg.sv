//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef OSC_PKG_SV
`define OSC_PKG_SV

package osc_pkg;

	`include "uvm_macros.svh"
	
	import uvm_pkg::*;
	
	import common_pkg::*;
	import common_env_pkg::*;
	
	// You can insert code here by setting agent_inc_inside_package in file osc.tpl
	
	`include "osc_tr.sv"
	`include "osc_config.sv"
	`include "osc_driver.sv"
	`include "osc_monitor.sv"
	`include "osc_sequencer.sv"
	`include "osc_coverage.sv"
	`include "osc_agent.sv"
	`include "osc_seq_lib.sv"
	
	// You can insert code here by setting agent_inc_after_all_includes in file osc.tpl

endpackage

`endif // OSC_PKG_SV
