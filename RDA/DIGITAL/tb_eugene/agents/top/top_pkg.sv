//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------

`ifndef TOP_PKG_SV
`define TOP_PKG_SV

package top_pkg;

	`include "uvm_macros.svh"

	import uvm_pkg::*;

	import regmodel_pkg::*;
	import test_regmodel_pkg::*;
	import common_pkg::*;
	import common_env_pkg::*;

	import buffer_reader_pkg::*;
	import buffer_writer_pkg::*;
	import digital_signal_pkg::*;
	import dsi3_master_pkg::*;
	import dsi3_slave_pkg::*;
	import elip_bus_pkg::*;
	import jtag_master_pkg::*;
	import osc_pkg::*;
	import pdcm_buffer_writer_pkg::*;
	import real_signal_pkg::*;
	import spi_pkg::*;

	`include "top_config.sv"
	`include "top_seq_lib.sv"
	`include "top_env.sv"

endpackage : top_pkg

`endif // TOP_PKG_SV