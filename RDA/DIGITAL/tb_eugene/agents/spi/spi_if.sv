//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef SPI_IF_SV
`define SPI_IF_SV

interface spi_if(); 

	timeunit      1ns;
	timeprecision 1ps;

	import common_pkg::*;
	import common_env_pkg::*;
	import spi_pkg::*;
	
	logic SCK;
	logic SDI;
	logic SDO;
	logic CSN;

	// You can insert properties and assertions here
	// You can insert code here by setting if_inc_inside_interface in file spi.tpl

endinterface

`endif
