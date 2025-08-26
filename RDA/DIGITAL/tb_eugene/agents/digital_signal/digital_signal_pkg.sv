//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef DIGITAL_SIGNAL_PKG_SV
`define DIGITAL_SIGNAL_PKG_SV

package digital_signal_pkg;

	`include "uvm_macros.svh"
	
	import uvm_pkg::*;
	
	import common_pkg::*;
	import common_env_pkg::*;
	
	// You can insert code here by setting agent_inc_inside_package in file digital_signal.tpl
	
	`include "digital_signal_tr.sv"
	`include "digital_signal_config.sv"
	`include "digital_signal_driver.sv"
	`include "digital_signal_monitor.sv"
	`include "digital_signal_sequencer.sv"
	`include "digital_signal_coverage.sv"
	`include "digital_signal_agent.sv"
	`include "digital_signal_seq_lib.sv"
	
	// You can insert code here by setting agent_inc_after_all_includes in file digital_signal.tpl

endpackage

`endif // DIGITAL_SIGNAL_PKG_SV
