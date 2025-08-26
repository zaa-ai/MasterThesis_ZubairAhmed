//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef ELIP_BUS_IF_SV
`define ELIP_BUS_IF_SV

interface elip_bus_if(); 

	timeunit      1ns;
	timeprecision 1ps;

	import common_pkg::*;
	import common_env_pkg::*;
	import elip_bus_pkg::*;
	
	parameter address_width = 16;
	parameter data_width = 16;
	parameter ecc_width = 6;
	logic ready;
	logic write;
	logic read;
	logic[data_width-1:0] data_read;
	logic[data_width-1:0] data_write;
	logic[ecc_width-1:0]  data_read_ecc;
	logic[ecc_width-1:0]  data_write_ecc;
	logic[address_width-1:0] address;
	logic clk;
	logic rstn;

	// You can insert properties and assertions here
	// You can insert code here by setting if_inc_inside_interface in file elip_bus.tpl

endinterface

`endif
