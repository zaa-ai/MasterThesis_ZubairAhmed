/**
 * Package: spi_unit_test_pkg
 * 
 * package for the SPI unit test
 */
package spi_unit_test_pkg;
	import uvm_pkg::*;
	import spi_pkg::*;
	import common_env_pkg::*;
	import project_pkg::*;

	`include "DW_ecc_function.inc"
	
	`include "test_builder.svh"
	`include "check_service.svh"
	`include "top_config.svh"
	`include "top_env.svh"
	`include "top_test.svh"
	`include "spi_test_seq.svh"

endpackage


