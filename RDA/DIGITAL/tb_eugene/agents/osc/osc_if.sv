//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef OSC_IF_SV
`define OSC_IF_SV

interface osc_if(); 

	timeunit      1ns;
	timeprecision 1ps;

	import common_pkg::*;
	import common_env_pkg::*;
	import osc_pkg::*;
	
	logic	CLK;
	logic	EN;

	// You can insert properties and assertions here
	// You can insert code here by setting if_inc_inside_interface in file osc.tpl

endinterface

`endif
