/**
 * Package: unit_test_pkg
 * 
 * package for unit testing
 */
package unit_test_pkg;
	import uvm_pkg::*;
	import addresses_pkg::*;
	import common_env_pkg::*;
	import elip_bus_pkg::*;
	import project_pkg::*;
	import main_control_pkg::*;
	import common_test_pkg::*;
	
	`uvm_analysis_imp_decl(_elip_writer)
	`uvm_analysis_imp_decl(_elip_register)
	
	`include "agent_factory.svh"
	`include "check_elip.svh"

	`include "top_config.svh"
	`include "top_env.svh"
	`include "top_test.svh"

endpackage


