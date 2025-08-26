//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------

module top_tb;

	timeunit       1ns;
	timeprecision  1ps;
	
	`include "uvm_macros.svh"

	import uvm_pkg::*;

	import common_pkg::*;
	import common_env_pkg::*;
	import top_pkg::*;
	import top_test_pkg::*;
	
	// Configuration object for top-level environment
	top_config top_env_config;

	// Test harness
	top_th th();
	
	// You can insert code here by setting tb_inc_inside_module in file common.tpl
	
	// You can remove the initial block below by setting tb_generate_run_test = no in file common.tpl
	initial begin
		// You can insert code here by setting tb_prepend_to_initial in file common.tpl

		// Create and populate top-level configuration object
		top_env_config = new("top_env_config");
		if ( !top_env_config.randomize() )
			`uvm_error("top_tb", "Failed to randomize top-level configuration object" )
		
		top_env_config.m_jtag_master_config.vif = th.jtag_master;
		top_env_config.m_spi_config.vif = th.spi;
		top_env_config.m_dsi3_slave_config[0].vif = th.dsi3_slave[0];					
		top_env_config.m_dsi3_slave_config[1].vif = th.dsi3_slave[1];					
		top_env_config.m_tmode_config.vif = th.tmode;
		top_env_config.m_resb_config.vif = th.resb;
		top_env_config.m_rfc_config.vif = th.rfc;
		top_env_config.m_bfwb_config.vif = th.bfwb;
		top_env_config.m_dab_config.vif = th.dab;
		top_env_config.m_intb_config.vif = th.intb;
		top_env_config.m_syncb_config.vif = th.syncb;
		top_env_config.m_syncb_out_config.vif = th.syncb_out;
		top_env_config.m_osc_config.vif = th.osc;
		top_env_config.m_iload_config[0].vif = th.iload[0];					
		top_env_config.m_iload_config[1].vif = th.iload[1];					
		top_env_config.m_vsup_config.vif = th.vsup;
		top_env_config.m_vcc_config.vif = th.vcc;
		top_env_config.m_vdd18_config.vif = th.vdd18;
		top_env_config.m_aout_config.vif = th.aout;
		top_env_config.m_ldo_config.vif = th.ldo;
		top_env_config.m_temp_config.vif = th.temp;
		
		uvm_config_db #(top_config)::set(null, "uvm_test_top", "config", top_env_config);
		uvm_config_db #(top_config)::set(null, "uvm_test_top.m_env", "config", top_env_config);
    
		`include "includes/tb_inc_before_run_test.sv"
		
		run_test();
	end
	
endmodule
