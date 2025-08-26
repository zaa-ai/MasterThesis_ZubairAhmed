//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef DSI3_SLAVE_IF_SV
`define DSI3_SLAVE_IF_SV

interface dsi3_slave_if(); 

	timeunit      1ns;
	timeprecision 1ps;

	import common_pkg::*;
	import common_env_pkg::*;
	import dsi3_slave_pkg::*;
	
	dsi3_pkg::dsi3_wire cable;

	// You can insert properties and assertions here
	// You can insert code here by setting if_inc_inside_interface in file dsi3_slave.tpl

endinterface

`endif
