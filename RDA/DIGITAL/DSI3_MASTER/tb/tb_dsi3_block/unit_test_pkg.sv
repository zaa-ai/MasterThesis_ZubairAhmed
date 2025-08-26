/**
 * Package: unit_test_pkg
 * 
 * package for unit testing
 */
package unit_test_pkg;
	import uvm_pkg::*;
	import common_pkg::*;
	import common_env_pkg::*;
	import buffer_if_pkg::*;
	import buffer_writer_pkg::*;
	import pdcm_buffer_writer_pkg::*;
	import buffer_reader_pkg::*;
	import spi_pkg::*;
	import elip_bus_pkg::*;
	import dsi3_slave_pkg::*;
	import dsi3_master_pkg::*;
	import dsi3_pkg::*;
	import project_pkg::*;
	import common_test_pkg::*;
	import digital_signal_pkg::*;
	import regmodel_pkg::*;
	
	typedef	struct {
		shortint	data;
		shortint	address;
	}	expected_elip_access_t;
	
	`include "dsi3_master_configuration_listener.svh"
	
	`uvm_analysis_imp_decl(_buffer_writer)
	`uvm_analysis_imp_decl(_elip_writer)
	`uvm_analysis_imp_decl(_frame_writer)
	`uvm_analysis_imp_decl(_dsi3_master)
	`uvm_analysis_imp_decl(_dsi3_slave)
	
	`include "default_comparer.svh"
	`include "agent_factory.svh"
	
	`include "check_elip_command_read_write.svh"
	`include "check_elip_tdma_access.svh"
	`include "check_transmit.svh"
	`include "check_receive.svh"
	`include "crm_check_receive.svh"
	`include "pdcm_check_receive.svh"
	`include "frame_facade.svh"
	
	`include "dsi3_slave_test_driver.svh"
	`include "dsi3_receiver_test_slave_sequence.svh"
	
	`include "top_config.svh"
	`include "top_env.svh"
	`include "top_test.svh"

endpackage


