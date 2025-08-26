//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef REAL_SIGNAL_IF_SV
`define REAL_SIGNAL_IF_SV

interface real_signal_if(); 

	timeunit      1ns;
	timeprecision 1ps;

	import common_pkg::*;
	import common_env_pkg::*;
	import real_signal_pkg::*;
	
	real PIN;

	// You can insert properties and assertions here
	// You can insert code here by setting if_inc_inside_interface in file real_signal.tpl

endinterface

`endif
