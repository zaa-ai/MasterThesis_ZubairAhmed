/**
 * Package: unit_test_pkg
 * 
 * package for unit testing
 */
package unit_test_pkg;
	import uvm_pkg::*;
	import common_pkg::*;
	import common_env_pkg::*;
	import elip_bus_pkg::*;
	import dsi3_pkg::*;
	import project_pkg::*;
	import common_test_pkg::*;
	import tdma_pkg::*;
	
	`uvm_analysis_imp_decl(_elip)
	
	`include "default_comparer.svh"
	`include "agent_factory.svh"
	
	`include "tdma_tr.svh"
	typedef uvm_sequencer #(tdma_tr) tdma_sequencer;
	`include "tdma_seq.svh"
	`include "tdma_header_seq.svh"
	`include "tdma_packet_seq.svh"
	`include "tdma_config.svh"
	`include "tdma_driver.svh"
	`include "tdma_agent.svh"
	`include "check_elip.svh"
	
	`include "top_config.svh"
	`include "top_env.svh"
	`include "top_test.svh"
	

endpackage


