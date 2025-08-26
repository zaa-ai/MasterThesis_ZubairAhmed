//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef JTAG_MASTER_PKG_SV
`define JTAG_MASTER_PKG_SV

package jtag_master_pkg;

	`include "uvm_macros.svh"
	
	import uvm_pkg::*;
	
	import common_pkg::*;
	import common_env_pkg::*;
	
	`include "includes/jtag_agent_inc_inside_package.svh"
	
	`include "jtag_master_tr.sv"
	`include "jtag_master_config.sv"
	`include "jtag_master_driver.sv"
	`include "jtag_master_monitor.sv"
	`include "jtag_master_sequencer.sv"
	`include "jtag_master_coverage.sv"
	`include "jtag_master_agent.sv"
	`include "jtag_master_seq_lib.sv"
	
	// You can insert code here by setting agent_inc_after_all_includes in file jtag_master.tpl

endpackage

`endif // JTAG_MASTER_PKG_SV
