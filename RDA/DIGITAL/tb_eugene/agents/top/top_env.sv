//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------


`ifndef TOP_ENV_SV
`define TOP_ENV_SV

`include "includes/top_env_inc_before_class.sv"

class top_env extends uvm_env;

  `uvm_component_utils(top_env)

  	function new(string name, uvm_component parent);
  		super.new(name, parent);
	endfunction : new
  
	// Child agents
	jtag_master_config m_jtag_master_config;
  	jtag_master_agent m_jtag_master_agent;
  	jtag_master_coverage m_jtag_master_coverage;
  	
	spi_config m_spi_config;
  	spi_agent m_spi_agent;
  	spi_coverage m_spi_coverage;
  	
	dsi3_master_config m_dsi3_master_config[1:0];
  	dsi3_master_agent m_dsi3_master_agent[1:0];
  	dsi3_master_coverage m_dsi3_master_coverage[1:0];
  	
	dsi3_slave_config m_dsi3_slave_config[1:0];
  	dsi3_slave_agent m_dsi3_slave_agent[1:0];
  	dsi3_slave_coverage m_dsi3_slave_coverage[1:0];
  	
	digital_signal_config m_tmode_config;
  	digital_signal_agent m_tmode_agent;
  	digital_signal_coverage m_tmode_coverage;
  	
	digital_signal_config m_resb_config;
  	digital_signal_agent m_resb_agent;
  	digital_signal_coverage m_resb_coverage;
  	
	digital_signal_config m_rfc_config;
  	digital_signal_agent m_rfc_agent;
  	digital_signal_coverage m_rfc_coverage;
  	
	digital_signal_config m_bfwb_config;
  	digital_signal_agent m_bfwb_agent;
  	digital_signal_coverage m_bfwb_coverage;
  	
	digital_signal_config m_dab_config;
  	digital_signal_agent m_dab_agent;
  	digital_signal_coverage m_dab_coverage;
  	
	digital_signal_config m_intb_config;
  	digital_signal_agent m_intb_agent;
  	digital_signal_coverage m_intb_coverage;
  	
	digital_signal_config m_syncb_config;
  	digital_signal_agent m_syncb_agent;
  	digital_signal_coverage m_syncb_coverage;
  	
	digital_signal_config m_syncb_out_config;
  	digital_signal_agent m_syncb_out_agent;
  	digital_signal_coverage m_syncb_out_coverage;
  	
	osc_config m_osc_config;
  	osc_agent m_osc_agent;
  	osc_coverage m_osc_coverage;
  	
	real_signal_config m_iload_config[1:0];
  	real_signal_agent m_iload_agent[1:0];
  	real_signal_coverage m_iload_coverage[1:0];
  	
	real_signal_config m_vsup_config;
  	real_signal_agent m_vsup_agent;
  	real_signal_coverage m_vsup_coverage;
  	
	real_signal_config m_vcc_config;
  	real_signal_agent m_vcc_agent;
  	real_signal_coverage m_vcc_coverage;
  	
	real_signal_config m_vdd18_config;
  	real_signal_agent m_vdd18_agent;
  	real_signal_coverage m_vdd18_coverage;
  	
	real_signal_config m_aout_config;
  	real_signal_agent m_aout_agent;
  	real_signal_coverage m_aout_coverage;
  	
	real_signal_config m_ldo_config;
  	real_signal_agent m_ldo_agent;
  	real_signal_coverage m_ldo_coverage;
  	
	real_signal_config m_temp_config;
  	real_signal_agent m_temp_agent;
  	real_signal_coverage m_temp_coverage;
  	
	ral_sys_device_registers regmodel;
	ral_sys_jtag_test_registers test_regmodel;
	top_config m_config;
   
	`include "includes/top_env_inc_inside_class.sv"

	// You can remove build/connect/run_phase by setting top_env_generate_methods_after_class = no in file common.tpl

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
  		`uvm_info(get_type_name(), "In build_phase", UVM_HIGH)

		// You can insert code here by setting top_env_prepend_to_build_phase in file common.tpl

		if (!uvm_config_db #(top_config)::get(this, "", "config", m_config)) begin 
			`uvm_error(get_type_name(), "Unable to get top_config")
		end
					
		regmodel = ral_sys_device_registers::type_id::create("regmodel");
  		regmodel.build();
		test_regmodel = ral_sys_jtag_test_registers::type_id::create("test_regmodel");
  		test_regmodel.build();
	
		// You can insert code here by setting agent_copy_config_vars in file jtag_master.tpl
		m_jtag_master_config = m_config.m_jtag_master_config;
		uvm_config_db #(jtag_master_config)::set(this, "m_jtag_master_agent", "config", m_jtag_master_config);
  		if (m_jtag_master_config.is_active == UVM_ACTIVE ) begin
    		uvm_config_db #(jtag_master_config)::set(this, "m_jtag_master_agent.m_sequencer", "config", m_jtag_master_config);
    	end
  		uvm_config_db #(jtag_master_config)::set(this, "m_jtag_master_coverage", "config", m_jtag_master_config);
		m_jtag_master_agent       = jtag_master_agent      ::type_id::create("m_jtag_master_agent", this);
  		m_jtag_master_coverage    = jtag_master_coverage   ::type_id::create("m_jtag_master_coverage", this);
		// You can insert code here by setting agent_copy_config_vars in file spi.tpl
		m_spi_config = m_config.m_spi_config;
		uvm_config_db #(spi_config)::set(this, "m_spi_agent", "config", m_spi_config);
  		if (m_spi_config.is_active == UVM_ACTIVE ) begin
    		uvm_config_db #(spi_config)::set(this, "m_spi_agent.m_sequencer", "config", m_spi_config);
    	end
  		uvm_config_db #(spi_config)::set(this, "m_spi_coverage", "config", m_spi_config);
		m_spi_agent       = spi_agent      ::type_id::create("m_spi_agent", this);
  		m_spi_coverage    = spi_coverage   ::type_id::create("m_spi_coverage", this);
		// You can insert code here by setting agent_copy_config_vars in file dsi3_master.tpl
		m_dsi3_master_config[0] = m_config.m_dsi3_master_config[0];
		uvm_config_db #(dsi3_master_config)::set(this, "m_dsi3_master_agent_0", "config", m_dsi3_master_config[0]);
  		if (m_dsi3_master_config[0].is_active == UVM_ACTIVE ) begin
    		uvm_config_db #(dsi3_master_config)::set(this, "m_dsi3_master_agent_0.m_sequencer", "config", m_dsi3_master_config[0]);
    	end
  		uvm_config_db #(dsi3_master_config)::set(this, "m_dsi3_master_coverage_0", "config", m_dsi3_master_config[0]);
		m_dsi3_master_agent[0]     = dsi3_master_agent      ::type_id::create("m_dsi3_master_agent_0", this);
  		m_dsi3_master_coverage[0]	= dsi3_master_coverage   ::type_id::create("m_dsi3_master_coverage_0", this);			
		m_dsi3_master_config[1] = m_config.m_dsi3_master_config[1];
		uvm_config_db #(dsi3_master_config)::set(this, "m_dsi3_master_agent_1", "config", m_dsi3_master_config[1]);
  		if (m_dsi3_master_config[1].is_active == UVM_ACTIVE ) begin
    		uvm_config_db #(dsi3_master_config)::set(this, "m_dsi3_master_agent_1.m_sequencer", "config", m_dsi3_master_config[1]);
    	end
  		uvm_config_db #(dsi3_master_config)::set(this, "m_dsi3_master_coverage_1", "config", m_dsi3_master_config[1]);
		m_dsi3_master_agent[1]     = dsi3_master_agent      ::type_id::create("m_dsi3_master_agent_1", this);
  		m_dsi3_master_coverage[1]	= dsi3_master_coverage   ::type_id::create("m_dsi3_master_coverage_1", this);			
		// You can insert code here by setting agent_copy_config_vars in file dsi3_slave.tpl
		m_dsi3_slave_config[0] = m_config.m_dsi3_slave_config[0];
		uvm_config_db #(dsi3_slave_config)::set(this, "m_dsi3_slave_agent_0", "config", m_dsi3_slave_config[0]);
  		if (m_dsi3_slave_config[0].is_active == UVM_ACTIVE ) begin
    		uvm_config_db #(dsi3_slave_config)::set(this, "m_dsi3_slave_agent_0.m_sequencer", "config", m_dsi3_slave_config[0]);
    	end
  		uvm_config_db #(dsi3_slave_config)::set(this, "m_dsi3_slave_coverage_0", "config", m_dsi3_slave_config[0]);
		m_dsi3_slave_agent[0]     = dsi3_slave_agent      ::type_id::create("m_dsi3_slave_agent_0", this);
  		m_dsi3_slave_coverage[0]	= dsi3_slave_coverage   ::type_id::create("m_dsi3_slave_coverage_0", this);			
		m_dsi3_slave_config[1] = m_config.m_dsi3_slave_config[1];
		uvm_config_db #(dsi3_slave_config)::set(this, "m_dsi3_slave_agent_1", "config", m_dsi3_slave_config[1]);
  		if (m_dsi3_slave_config[1].is_active == UVM_ACTIVE ) begin
    		uvm_config_db #(dsi3_slave_config)::set(this, "m_dsi3_slave_agent_1.m_sequencer", "config", m_dsi3_slave_config[1]);
    	end
  		uvm_config_db #(dsi3_slave_config)::set(this, "m_dsi3_slave_coverage_1", "config", m_dsi3_slave_config[1]);
		m_dsi3_slave_agent[1]     = dsi3_slave_agent      ::type_id::create("m_dsi3_slave_agent_1", this);
  		m_dsi3_slave_coverage[1]	= dsi3_slave_coverage   ::type_id::create("m_dsi3_slave_coverage_1", this);			
		// You can insert code here by setting agent_copy_config_vars in file digital_signal.tpl
		m_tmode_config = m_config.m_tmode_config;
		uvm_config_db #(digital_signal_config)::set(this, "m_tmode_agent", "config", m_tmode_config);
  		if (m_tmode_config.is_active == UVM_ACTIVE ) begin
    		uvm_config_db #(digital_signal_config)::set(this, "m_tmode_agent.m_sequencer", "config", m_tmode_config);
    	end
  		uvm_config_db #(digital_signal_config)::set(this, "m_tmode_coverage", "config", m_tmode_config);
		m_tmode_agent       = digital_signal_agent      ::type_id::create("m_tmode_agent", this);
  		m_tmode_coverage    = digital_signal_coverage   ::type_id::create("m_tmode_coverage", this);
		// You can insert code here by setting agent_copy_config_vars in file digital_signal.tpl
		m_resb_config = m_config.m_resb_config;
		uvm_config_db #(digital_signal_config)::set(this, "m_resb_agent", "config", m_resb_config);
  		if (m_resb_config.is_active == UVM_ACTIVE ) begin
    		uvm_config_db #(digital_signal_config)::set(this, "m_resb_agent.m_sequencer", "config", m_resb_config);
    	end
  		uvm_config_db #(digital_signal_config)::set(this, "m_resb_coverage", "config", m_resb_config);
		m_resb_agent       = digital_signal_agent      ::type_id::create("m_resb_agent", this);
  		m_resb_coverage    = digital_signal_coverage   ::type_id::create("m_resb_coverage", this);
		// You can insert code here by setting agent_copy_config_vars in file digital_signal.tpl
		m_rfc_config = m_config.m_rfc_config;
		uvm_config_db #(digital_signal_config)::set(this, "m_rfc_agent", "config", m_rfc_config);
  		if (m_rfc_config.is_active == UVM_ACTIVE ) begin
    		uvm_config_db #(digital_signal_config)::set(this, "m_rfc_agent.m_sequencer", "config", m_rfc_config);
    	end
  		uvm_config_db #(digital_signal_config)::set(this, "m_rfc_coverage", "config", m_rfc_config);
		m_rfc_agent       = digital_signal_agent      ::type_id::create("m_rfc_agent", this);
  		m_rfc_coverage    = digital_signal_coverage   ::type_id::create("m_rfc_coverage", this);
		// You can insert code here by setting agent_copy_config_vars in file digital_signal.tpl
		m_bfwb_config = m_config.m_bfwb_config;
		uvm_config_db #(digital_signal_config)::set(this, "m_bfwb_agent", "config", m_bfwb_config);
  		if (m_bfwb_config.is_active == UVM_ACTIVE ) begin
    		uvm_config_db #(digital_signal_config)::set(this, "m_bfwb_agent.m_sequencer", "config", m_bfwb_config);
    	end
  		uvm_config_db #(digital_signal_config)::set(this, "m_bfwb_coverage", "config", m_bfwb_config);
		m_bfwb_agent       = digital_signal_agent      ::type_id::create("m_bfwb_agent", this);
  		m_bfwb_coverage    = digital_signal_coverage   ::type_id::create("m_bfwb_coverage", this);
		// You can insert code here by setting agent_copy_config_vars in file digital_signal.tpl
		m_dab_config = m_config.m_dab_config;
		uvm_config_db #(digital_signal_config)::set(this, "m_dab_agent", "config", m_dab_config);
  		if (m_dab_config.is_active == UVM_ACTIVE ) begin
    		uvm_config_db #(digital_signal_config)::set(this, "m_dab_agent.m_sequencer", "config", m_dab_config);
    	end
  		uvm_config_db #(digital_signal_config)::set(this, "m_dab_coverage", "config", m_dab_config);
		m_dab_agent       = digital_signal_agent      ::type_id::create("m_dab_agent", this);
  		m_dab_coverage    = digital_signal_coverage   ::type_id::create("m_dab_coverage", this);
		// You can insert code here by setting agent_copy_config_vars in file digital_signal.tpl
		m_intb_config = m_config.m_intb_config;
		uvm_config_db #(digital_signal_config)::set(this, "m_intb_agent", "config", m_intb_config);
  		if (m_intb_config.is_active == UVM_ACTIVE ) begin
    		uvm_config_db #(digital_signal_config)::set(this, "m_intb_agent.m_sequencer", "config", m_intb_config);
    	end
  		uvm_config_db #(digital_signal_config)::set(this, "m_intb_coverage", "config", m_intb_config);
		m_intb_agent       = digital_signal_agent      ::type_id::create("m_intb_agent", this);
  		m_intb_coverage    = digital_signal_coverage   ::type_id::create("m_intb_coverage", this);
		// You can insert code here by setting agent_copy_config_vars in file digital_signal.tpl
		m_syncb_config = m_config.m_syncb_config;
		uvm_config_db #(digital_signal_config)::set(this, "m_syncb_agent", "config", m_syncb_config);
  		if (m_syncb_config.is_active == UVM_ACTIVE ) begin
    		uvm_config_db #(digital_signal_config)::set(this, "m_syncb_agent.m_sequencer", "config", m_syncb_config);
    	end
  		uvm_config_db #(digital_signal_config)::set(this, "m_syncb_coverage", "config", m_syncb_config);
		m_syncb_agent       = digital_signal_agent      ::type_id::create("m_syncb_agent", this);
  		m_syncb_coverage    = digital_signal_coverage   ::type_id::create("m_syncb_coverage", this);
		// You can insert code here by setting agent_copy_config_vars in file digital_signal.tpl
		m_syncb_out_config = m_config.m_syncb_out_config;
		uvm_config_db #(digital_signal_config)::set(this, "m_syncb_out_agent", "config", m_syncb_out_config);
  		if (m_syncb_out_config.is_active == UVM_ACTIVE ) begin
    		uvm_config_db #(digital_signal_config)::set(this, "m_syncb_out_agent.m_sequencer", "config", m_syncb_out_config);
    	end
  		uvm_config_db #(digital_signal_config)::set(this, "m_syncb_out_coverage", "config", m_syncb_out_config);
		m_syncb_out_agent       = digital_signal_agent      ::type_id::create("m_syncb_out_agent", this);
  		m_syncb_out_coverage    = digital_signal_coverage   ::type_id::create("m_syncb_out_coverage", this);
		// You can insert code here by setting agent_copy_config_vars in file osc.tpl
		m_osc_config = m_config.m_osc_config;
		uvm_config_db #(osc_config)::set(this, "m_osc_agent", "config", m_osc_config);
  		if (m_osc_config.is_active == UVM_ACTIVE ) begin
    		uvm_config_db #(osc_config)::set(this, "m_osc_agent.m_sequencer", "config", m_osc_config);
    	end
  		uvm_config_db #(osc_config)::set(this, "m_osc_coverage", "config", m_osc_config);
		m_osc_agent       = osc_agent      ::type_id::create("m_osc_agent", this);
  		m_osc_coverage    = osc_coverage   ::type_id::create("m_osc_coverage", this);
		// You can insert code here by setting agent_copy_config_vars in file real_signal.tpl
		m_iload_config[0] = m_config.m_iload_config[0];
		uvm_config_db #(real_signal_config)::set(this, "m_iload_agent_0", "config", m_iload_config[0]);
  		if (m_iload_config[0].is_active == UVM_ACTIVE ) begin
    		uvm_config_db #(real_signal_config)::set(this, "m_iload_agent_0.m_sequencer", "config", m_iload_config[0]);
    	end
  		uvm_config_db #(real_signal_config)::set(this, "m_iload_coverage_0", "config", m_iload_config[0]);
		m_iload_agent[0]     = real_signal_agent      ::type_id::create("m_iload_agent_0", this);
  		m_iload_coverage[0]	= real_signal_coverage   ::type_id::create("m_iload_coverage_0", this);			
		m_iload_config[1] = m_config.m_iload_config[1];
		uvm_config_db #(real_signal_config)::set(this, "m_iload_agent_1", "config", m_iload_config[1]);
  		if (m_iload_config[1].is_active == UVM_ACTIVE ) begin
    		uvm_config_db #(real_signal_config)::set(this, "m_iload_agent_1.m_sequencer", "config", m_iload_config[1]);
    	end
  		uvm_config_db #(real_signal_config)::set(this, "m_iload_coverage_1", "config", m_iload_config[1]);
		m_iload_agent[1]     = real_signal_agent      ::type_id::create("m_iload_agent_1", this);
  		m_iload_coverage[1]	= real_signal_coverage   ::type_id::create("m_iload_coverage_1", this);			
		// You can insert code here by setting agent_copy_config_vars in file real_signal.tpl
		m_vsup_config = m_config.m_vsup_config;
		uvm_config_db #(real_signal_config)::set(this, "m_vsup_agent", "config", m_vsup_config);
  		if (m_vsup_config.is_active == UVM_ACTIVE ) begin
    		uvm_config_db #(real_signal_config)::set(this, "m_vsup_agent.m_sequencer", "config", m_vsup_config);
    	end
  		uvm_config_db #(real_signal_config)::set(this, "m_vsup_coverage", "config", m_vsup_config);
		m_vsup_agent       = real_signal_agent      ::type_id::create("m_vsup_agent", this);
  		m_vsup_coverage    = real_signal_coverage   ::type_id::create("m_vsup_coverage", this);
		// You can insert code here by setting agent_copy_config_vars in file real_signal.tpl
		m_vcc_config = m_config.m_vcc_config;
		uvm_config_db #(real_signal_config)::set(this, "m_vcc_agent", "config", m_vcc_config);
  		if (m_vcc_config.is_active == UVM_ACTIVE ) begin
    		uvm_config_db #(real_signal_config)::set(this, "m_vcc_agent.m_sequencer", "config", m_vcc_config);
    	end
  		uvm_config_db #(real_signal_config)::set(this, "m_vcc_coverage", "config", m_vcc_config);
		m_vcc_agent       = real_signal_agent      ::type_id::create("m_vcc_agent", this);
  		m_vcc_coverage    = real_signal_coverage   ::type_id::create("m_vcc_coverage", this);
		// You can insert code here by setting agent_copy_config_vars in file real_signal.tpl
		m_vdd18_config = m_config.m_vdd18_config;
		uvm_config_db #(real_signal_config)::set(this, "m_vdd18_agent", "config", m_vdd18_config);
  		if (m_vdd18_config.is_active == UVM_ACTIVE ) begin
    		uvm_config_db #(real_signal_config)::set(this, "m_vdd18_agent.m_sequencer", "config", m_vdd18_config);
    	end
  		uvm_config_db #(real_signal_config)::set(this, "m_vdd18_coverage", "config", m_vdd18_config);
		m_vdd18_agent       = real_signal_agent      ::type_id::create("m_vdd18_agent", this);
  		m_vdd18_coverage    = real_signal_coverage   ::type_id::create("m_vdd18_coverage", this);
		// You can insert code here by setting agent_copy_config_vars in file real_signal.tpl
		m_aout_config = m_config.m_aout_config;
		uvm_config_db #(real_signal_config)::set(this, "m_aout_agent", "config", m_aout_config);
  		if (m_aout_config.is_active == UVM_ACTIVE ) begin
    		uvm_config_db #(real_signal_config)::set(this, "m_aout_agent.m_sequencer", "config", m_aout_config);
    	end
  		uvm_config_db #(real_signal_config)::set(this, "m_aout_coverage", "config", m_aout_config);
		m_aout_agent       = real_signal_agent      ::type_id::create("m_aout_agent", this);
  		m_aout_coverage    = real_signal_coverage   ::type_id::create("m_aout_coverage", this);
		// You can insert code here by setting agent_copy_config_vars in file real_signal.tpl
		m_ldo_config = m_config.m_ldo_config;
		uvm_config_db #(real_signal_config)::set(this, "m_ldo_agent", "config", m_ldo_config);
  		if (m_ldo_config.is_active == UVM_ACTIVE ) begin
    		uvm_config_db #(real_signal_config)::set(this, "m_ldo_agent.m_sequencer", "config", m_ldo_config);
    	end
  		uvm_config_db #(real_signal_config)::set(this, "m_ldo_coverage", "config", m_ldo_config);
		m_ldo_agent       = real_signal_agent      ::type_id::create("m_ldo_agent", this);
  		m_ldo_coverage    = real_signal_coverage   ::type_id::create("m_ldo_coverage", this);
		// You can insert code here by setting agent_copy_config_vars in file real_signal.tpl
		m_temp_config = m_config.m_temp_config;
		uvm_config_db #(real_signal_config)::set(this, "m_temp_agent", "config", m_temp_config);
  		if (m_temp_config.is_active == UVM_ACTIVE ) begin
    		uvm_config_db #(real_signal_config)::set(this, "m_temp_agent.m_sequencer", "config", m_temp_config);
    	end
  		uvm_config_db #(real_signal_config)::set(this, "m_temp_coverage", "config", m_temp_config);
		m_temp_agent       = real_signal_agent      ::type_id::create("m_temp_agent", this);
  		m_temp_coverage    = real_signal_coverage   ::type_id::create("m_temp_coverage", this);

		`include "includes/top_env_append_to_build_phase.sv"

	endfunction : build_phase
	
	function void connect_phase(uvm_phase phase);
		`uvm_info(get_type_name(), "In connect_phase", UVM_HIGH)

		m_jtag_master_agent.analysis_port.connect(m_jtag_master_coverage.analysis_export);		
		m_spi_agent.analysis_port.connect(m_spi_coverage.analysis_export);		
		m_dsi3_master_agent[0].analysis_port.connect(m_dsi3_master_coverage[0].analysis_export);
		m_dsi3_master_agent[1].analysis_port.connect(m_dsi3_master_coverage[1].analysis_export);
		m_dsi3_slave_agent[0].analysis_port.connect(m_dsi3_slave_coverage[0].analysis_export);
		m_dsi3_slave_agent[1].analysis_port.connect(m_dsi3_slave_coverage[1].analysis_export);
		m_tmode_agent.analysis_port.connect(m_tmode_coverage.analysis_export);		
		m_resb_agent.analysis_port.connect(m_resb_coverage.analysis_export);		
		m_rfc_agent.analysis_port.connect(m_rfc_coverage.analysis_export);		
		m_bfwb_agent.analysis_port.connect(m_bfwb_coverage.analysis_export);		
		m_dab_agent.analysis_port.connect(m_dab_coverage.analysis_export);		
		m_intb_agent.analysis_port.connect(m_intb_coverage.analysis_export);		
		m_syncb_agent.analysis_port.connect(m_syncb_coverage.analysis_export);		
		m_syncb_out_agent.analysis_port.connect(m_syncb_out_coverage.analysis_export);		
		m_osc_agent.analysis_port.connect(m_osc_coverage.analysis_export);		
		m_iload_agent[0].analysis_port.connect(m_iload_coverage[0].analysis_export);
		m_iload_agent[1].analysis_port.connect(m_iload_coverage[1].analysis_export);
		m_vsup_agent.analysis_port.connect(m_vsup_coverage.analysis_export);		
		m_vcc_agent.analysis_port.connect(m_vcc_coverage.analysis_export);		
		m_vdd18_agent.analysis_port.connect(m_vdd18_coverage.analysis_export);		
		m_aout_agent.analysis_port.connect(m_aout_coverage.analysis_export);		
		m_ldo_agent.analysis_port.connect(m_ldo_coverage.analysis_export);		
		m_temp_agent.analysis_port.connect(m_temp_coverage.analysis_export);		
		// Connect the register model in each agent's env

		`include "includes/top_env_append_to_connect_phase.sv"

	endfunction : connect_phase

	task run_phase(uvm_phase phase);
  		top_default_seq vseq;
  		vseq = top_default_seq::type_id::create("vseq");
  		vseq.set_item_context(null, null);
  		if ( !vseq.randomize() ) begin
			`uvm_fatal(get_type_name(), "Failed to randomize virtual sequence")
		end

		vseq.m_jtag_master_agent = m_jtag_master_agent;
		vseq.jtag_master = m_jtag_master_agent.m_config.vif;
		vseq.m_spi_agent = m_spi_agent;
		vseq.spi = m_spi_agent.m_config.vif;
		vseq.m_dsi3_master_agent[0] = m_dsi3_master_agent[0];
		vseq.m_dsi3_master_agent[1] = m_dsi3_master_agent[1];
		vseq.m_dsi3_slave_agent[0] = m_dsi3_slave_agent[0];
		vseq.dsi3_slave[0] = m_dsi3_slave_agent[0].m_config.vif;
		vseq.m_dsi3_slave_agent[1] = m_dsi3_slave_agent[1];
		vseq.dsi3_slave[1] = m_dsi3_slave_agent[1].m_config.vif;
		vseq.m_tmode_agent = m_tmode_agent;
		vseq.tmode = m_tmode_agent.m_config.vif;
		vseq.m_resb_agent = m_resb_agent;
		vseq.resb = m_resb_agent.m_config.vif;
		vseq.m_rfc_agent = m_rfc_agent;
		vseq.rfc = m_rfc_agent.m_config.vif;
		vseq.m_bfwb_agent = m_bfwb_agent;
		vseq.bfwb = m_bfwb_agent.m_config.vif;
		vseq.m_dab_agent = m_dab_agent;
		vseq.dab = m_dab_agent.m_config.vif;
		vseq.m_intb_agent = m_intb_agent;
		vseq.intb = m_intb_agent.m_config.vif;
		vseq.m_syncb_agent = m_syncb_agent;
		vseq.syncb = m_syncb_agent.m_config.vif;
		vseq.m_syncb_out_agent = m_syncb_out_agent;
		vseq.syncb_out = m_syncb_out_agent.m_config.vif;
		vseq.m_osc_agent = m_osc_agent;
		vseq.osc = m_osc_agent.m_config.vif;
		vseq.m_iload_agent[0] = m_iload_agent[0];
		vseq.iload[0] = m_iload_agent[0].m_config.vif;
		vseq.m_iload_agent[1] = m_iload_agent[1];
		vseq.iload[1] = m_iload_agent[1].m_config.vif;
		vseq.m_vsup_agent = m_vsup_agent;
		vseq.vsup = m_vsup_agent.m_config.vif;
		vseq.m_vcc_agent = m_vcc_agent;
		vseq.vcc = m_vcc_agent.m_config.vif;
		vseq.m_vdd18_agent = m_vdd18_agent;
		vseq.vdd18 = m_vdd18_agent.m_config.vif;
		vseq.m_aout_agent = m_aout_agent;
		vseq.aout = m_aout_agent.m_config.vif;
		vseq.m_ldo_agent = m_ldo_agent;
		vseq.ldo = m_ldo_agent.m_config.vif;
		vseq.m_temp_agent = m_temp_agent;
		vseq.temp = m_temp_agent.m_config.vif;
  		vseq.regmodel = regmodel;
  		vseq.test_regmodel = test_regmodel;
		vseq.m_config = m_config;                
		vseq.set_starting_phase(phase);
		vseq.start(null);

		// You can insert code here by setting top_env_append_to_run_phase in file common.tpl

	endtask : run_phase	

endclass : top_env 

// You can insert code here by setting top_env_inc_after_class in file common.tpl

`endif // TOP_ENV_SV
