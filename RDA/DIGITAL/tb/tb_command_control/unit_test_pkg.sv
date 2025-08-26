/**
 * Package: unit_test_pkg
 *
 * package for unit testing
 */
package unit_test_pkg;
	import uvm_pkg::*;
	import common_env_pkg::*;
	import buffer_if_pkg::*;
	import buffer_reader_pkg::*;
	import buffer_writer_pkg::*;
	import elip_bus_pkg::*;
	import spi_pkg::*;
	import project_pkg::*;

	`include "DW_ecc_function.inc"

	`uvm_analysis_imp_decl(_buffer_writer)
	`uvm_analysis_imp_decl(_elip_writer)
	`uvm_analysis_imp_decl(_frame_writer)

	`include "default_comparer.svh"
	`include "frame_facade.svh"
	`include "check_register_write.svh"
	`include "check_elip_command_write.svh"
	`include "check_dsi_command_writes.svh"

	`include "top_config.svh"
	`include "top_env.svh"
	`include "top_test.svh"

endpackage


