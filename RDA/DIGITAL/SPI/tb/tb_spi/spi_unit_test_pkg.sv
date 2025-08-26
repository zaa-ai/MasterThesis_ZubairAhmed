/**
 * Package: spi_unit_test_pkg
 * 
 * package for the SPI unit test
 */
package spi_unit_test_pkg;
	import uvm_pkg::*;
	import spi_pkg::*;
	import common_env_pkg::*;
	import elip_bus_pkg::*;
	import buffer_if_pkg::*;
	import buffer_reader_pkg::*;
	import buffer_writer_pkg::*;
	import pdcm_buffer_writer_pkg::*;
	import project_pkg::*;
	
	`include "DW_ecc_function.inc"

	`uvm_analysis_imp_decl(_elip)
	`uvm_analysis_imp_decl(_frame)
	
	`include "agent_factory.svh"
	`include "packet_creator.svh"
	`include "check_register_reads.svh"
	`include "command_buffer_creator.svh"
	`include "components/behaviour_checker.svh"
    `include "in_order_buffer_comparator.sv"
	`include "top_config.svh"
	`include "top_env.svh"
	`include "top_test.svh"
	`include "spi_test_seq.svh"

endpackage


