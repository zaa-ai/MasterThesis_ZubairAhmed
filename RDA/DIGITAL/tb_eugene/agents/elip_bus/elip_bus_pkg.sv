//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef ELIP_BUS_PKG_SV
`define ELIP_BUS_PKG_SV

package elip_bus_pkg;

	`include "uvm_macros.svh"
	
	import uvm_pkg::*;
	
	import common_pkg::*;
	import common_env_pkg::*;
	
	// You can insert code here by setting agent_inc_inside_package in file elip_bus.tpl
	
	`include "elip_bus_tr.sv"
	`include "elip_bus_config.sv"
	`include "elip_bus_driver.sv"
	`include "elip_bus_monitor.sv"
	`include "elip_bus_sequencer.sv"
	`include "elip_bus_coverage.sv"
	`include "elip_bus_agent.sv"
	`include "elip_bus_seq_lib.sv"
	
	// You can insert code here by setting agent_inc_after_all_includes in file elip_bus.tpl

endpackage

`endif // ELIP_BUS_PKG_SV
