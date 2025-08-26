//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef REAL_SIGNAL_PKG_SV
`define REAL_SIGNAL_PKG_SV

package real_signal_pkg;

	`include "uvm_macros.svh"
	
	import uvm_pkg::*;
	
	import common_pkg::*;
	import common_env_pkg::*;
	
	// You can insert code here by setting agent_inc_inside_package in file real_signal.tpl
	
	`include "real_signal_tr.sv"
	`include "real_signal_config.sv"
	`include "real_signal_driver.sv"
	`include "real_signal_monitor.sv"
	`include "real_signal_sequencer.sv"
	`include "real_signal_coverage.sv"
	`include "real_signal_agent.sv"
	`include "real_signal_seq_lib.sv"
	
	// You can insert code here by setting agent_inc_after_all_includes in file real_signal.tpl

endpackage

`endif // REAL_SIGNAL_PKG_SV
