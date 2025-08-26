/**
 * Package: common_env_pkg
 *
 * Common package for class based items
 */
package common_env_pkg;
	import uvm_pkg::*;
	import common_pkg::*;
	import crc_calculation_pkg::*;

	`uvm_analysis_imp_decl(_resb)
	`uvm_analysis_imp_decl(_rfc)
	`uvm_analysis_imp_decl(_configuration)

	`uvm_analysis_imp_decl(_spi_read_crm_data_packets)
	`uvm_analysis_imp_decl(_spi_read_pdcm_frame)

	`uvm_analysis_imp_decl(_dsi3_master_tr)
	`uvm_analysis_imp_decl(_dsi3_slave_tr)

	typedef enum {
		/**
		 * Generate an error in every case.
		 */
		ALWAYS_ERROR=0,
		/**
		 * Never generate an error.
		 */
		NEVER_ERROR=1,
		/**
		 * Generate error randomly.
		 */
		RANDOM_ERROR,
		/**
		 * No error injection strategy has been defined yet.
		 */
		NOT_SET
	} error_injection_e;

	`include "common_functions.svh"
	`include "simulation_logger.svh"
	`include "register_util.svh"
	`include "otp_writer.svh"

	`include "dsi3_packet.svh"
	`include "dsi3_crm_packet.svh"
	`include "dsi3_pdcm_packet.svh"

	`include "dsi3_master_configuration_tr.svh"
	`include "dsi3_master_configuration_subscriber.svh"

	`include "tdma_scheme_packet.svh"
	`include "tdma_scheme_packet_crm.svh"
	`include "tdma_scheme_packet_pdcm.svh"
	`include "tdma_scheme_packet_dm.svh"
	
	`include "tdma_scheme.svh"
	`include "tdma_scheme_crm.svh"
	`include "tdma_scheme_dm.svh"
	`include "tdma_scheme_pdcm.svh"
	`include "tdma_scheme_pdcm_denso.svh"
	`include "tdma_scheme_pdcm_denso_15.svh"
	`include "tdma_scheme_pdcm_factory.svh"
	`include "checker_config.svh"

endpackage


