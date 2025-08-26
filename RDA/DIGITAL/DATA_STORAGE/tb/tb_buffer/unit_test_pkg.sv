/**
 * Package: unit_test_pkg
 * 
 * package for unit testing
 */
package unit_test_pkg;
	import uvm_pkg::*;
	import common_env_pkg::*;
	import buffer_reader_pkg::*;
	import buffer_if_pkg::*;
	import buffer_writer_pkg::*;
	import project_pkg::*;
	import elip_bus_pkg::*;

	`uvm_analysis_imp_decl(_reader)
	`uvm_analysis_imp_decl(_writer)
	`uvm_analysis_imp_decl(_elip)
	
	`include "buffer_object.svh"
	`include "check_service.svh"
	
	`include "top_config.svh"
	`include "top_env.svh"
	`include "top_test.svh"

endpackage


