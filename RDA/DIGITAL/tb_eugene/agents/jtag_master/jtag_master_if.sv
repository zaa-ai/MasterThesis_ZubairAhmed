//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef JTAG_MASTER_IF_SV
`define JTAG_MASTER_IF_SV

interface jtag_master_if(); 

	timeunit      1ns;
	timeprecision 1ps;

	import common_pkg::*;
	import common_env_pkg::*;
	import jtag_master_pkg::*;
	
	logic TRST;
	logic TCK;
	logic TDI;
	logic TMS;
	wire TDO;

	// You can insert properties and assertions here
	// You can insert code here by setting if_inc_inside_interface in file jtag_master.tpl

endinterface

`endif
