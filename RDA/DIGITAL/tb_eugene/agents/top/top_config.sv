//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------

`ifndef TOP_CONFIG_SV
`define TOP_CONFIG_SV

`include "includes/top_env_config_inc_before_class.sv"

class top_config extends uvm_object;

	// Do not register config class with the factory
	
	rand jtag_master_config m_jtag_master_config;
	rand spi_config m_spi_config;
	rand dsi3_master_config m_dsi3_master_config[1:0];		
	rand dsi3_slave_config m_dsi3_slave_config[1:0];		
	rand digital_signal_config m_tmode_config;
	rand digital_signal_config m_resb_config;
	rand digital_signal_config m_rfc_config;
	rand digital_signal_config m_bfwb_config;
	rand digital_signal_config m_dab_config;
	rand digital_signal_config m_intb_config;
	rand digital_signal_config m_syncb_config;
	rand digital_signal_config m_syncb_out_config;
	rand osc_config m_osc_config;
	rand real_signal_config m_iload_config[1:0];		
	rand real_signal_config m_vsup_config;
	rand real_signal_config m_vcc_config;
	rand real_signal_config m_vdd18_config;
	rand real_signal_config m_aout_config;
	rand real_signal_config m_ldo_config;
	rand real_signal_config m_temp_config;
	
	
	// You can remove new by setting top_env_config_generate_methods_inside_class = no in file common.tpl
	
	function new(string name = "");
		super.new(name);
		
		m_jtag_master_config = new("m_jtag_master_config");
		m_jtag_master_config.is_active       = UVM_ACTIVE;
		m_jtag_master_config.coverage_enable = 1;
		m_spi_config = new("m_spi_config");
		m_spi_config.is_active       = UVM_ACTIVE;
		m_spi_config.coverage_enable = 1;
		m_dsi3_master_config[0] = new("m_dsi3_master_config_[0]");
		m_dsi3_master_config[0].is_active       =  UVM_PASSIVE;
		m_dsi3_master_config[0].coverage_enable = 1;
		m_dsi3_master_config[1] = new("m_dsi3_master_config_[1]");
		m_dsi3_master_config[1].is_active       =  UVM_PASSIVE;
		m_dsi3_master_config[1].coverage_enable = 1;
		m_dsi3_slave_config[0] = new("m_dsi3_slave_config_[0]");
		m_dsi3_slave_config[0].is_active       = UVM_ACTIVE;
		m_dsi3_slave_config[0].coverage_enable = 1;
		m_dsi3_slave_config[1] = new("m_dsi3_slave_config_[1]");
		m_dsi3_slave_config[1].is_active       = UVM_ACTIVE;
		m_dsi3_slave_config[1].coverage_enable = 1;
		m_tmode_config = new("m_tmode_config");
		m_tmode_config.is_active       = UVM_ACTIVE;
		m_tmode_config.coverage_enable = 1;
		m_resb_config = new("m_resb_config");
		m_resb_config.is_active       = UVM_ACTIVE;
		m_resb_config.coverage_enable = 1;
		m_rfc_config = new("m_rfc_config");
		m_rfc_config.is_active       = UVM_ACTIVE;
		m_rfc_config.coverage_enable = 1;
		m_bfwb_config = new("m_bfwb_config");
		m_bfwb_config.is_active       = UVM_ACTIVE;
		m_bfwb_config.coverage_enable = 1;
		m_dab_config = new("m_dab_config");
		m_dab_config.is_active       = UVM_ACTIVE;
		m_dab_config.coverage_enable = 1;
		m_intb_config = new("m_intb_config");
		m_intb_config.is_active       = UVM_ACTIVE;
		m_intb_config.coverage_enable = 1;
		m_syncb_config = new("m_syncb_config");
		m_syncb_config.is_active       = UVM_ACTIVE;
		m_syncb_config.coverage_enable = 1;
		m_syncb_out_config = new("m_syncb_out_config");
		m_syncb_out_config.is_active       =  UVM_PASSIVE;
		m_syncb_out_config.coverage_enable = 1;
		m_osc_config = new("m_osc_config");
		m_osc_config.is_active       = UVM_ACTIVE;
		m_osc_config.coverage_enable = 1;
		m_iload_config[0] = new("m_iload_config_[0]");
		m_iload_config[0].is_active       = UVM_ACTIVE;
		m_iload_config[0].coverage_enable = 1;
		m_iload_config[1] = new("m_iload_config_[1]");
		m_iload_config[1].is_active       = UVM_ACTIVE;
		m_iload_config[1].coverage_enable = 1;
		m_vsup_config = new("m_vsup_config");
		m_vsup_config.is_active       = UVM_ACTIVE;
		m_vsup_config.coverage_enable = 1;
		m_vcc_config = new("m_vcc_config");
		m_vcc_config.is_active       = UVM_ACTIVE;
		m_vcc_config.coverage_enable = 1;
		m_vdd18_config = new("m_vdd18_config");
		m_vdd18_config.is_active       = UVM_ACTIVE;
		m_vdd18_config.coverage_enable = 1;
		m_aout_config = new("m_aout_config");
		m_aout_config.is_active       = UVM_ACTIVE;
		m_aout_config.coverage_enable = 1;
		m_ldo_config = new("m_ldo_config");
		m_ldo_config.is_active       = UVM_ACTIVE;
		m_ldo_config.coverage_enable = 1;
		m_temp_config = new("m_temp_config");
		m_temp_config.is_active       = UVM_ACTIVE;
		m_temp_config.coverage_enable = 1;

		// You can insert code here by setting top_env_config_append_to_new in file common.tpl
	
	endfunction : new

	// You can insert code here by setting top_env_config_inc_inside_class in file common.tpl

endclass : top_config 

// You can insert code here by setting top_env_config_inc_after_class in file common.tpl

`endif // TOP_CONFIG_SV

