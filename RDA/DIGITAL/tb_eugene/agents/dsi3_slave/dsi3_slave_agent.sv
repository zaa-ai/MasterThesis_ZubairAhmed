//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef DSI3_SLAVE_AGENT_SV
`define DSI3_SLAVE_AGENT_SV

// You can insert code here by setting agent_inc_before_class in file dsi3_slave.tpl

class dsi3_slave_agent extends uvm_agent;

	`uvm_component_utils(dsi3_slave_agent)

	uvm_analysis_port #(dsi3_slave_tr) analysis_port;

	dsi3_slave_config	m_config;
	dsi3_slave_sequencer	m_sequencer;
	dsi3_slave_driver	m_driver;
	dsi3_slave_monitor	m_monitor;

	local int m_is_active = -1;

	function	new(string name, uvm_component parent);
		super.new(name, parent);
		analysis_port = new("analysis_port", this);
	endfunction

	// You can remove build/connect_phase and get_is_active by setting agent_generate_methods_after_class = no in file dsi3_slave.tpl
	
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		
		// You can insert code here by setting agent_prepend_to_build_phase in file dsi3_slave.tpl

		if (!uvm_config_db #(dsi3_slave_config)::get(this, "", "config", m_config))
			`uvm_error(get_type_name(), "dsi3_slave config not found")

		m_monitor	= dsi3_slave_monitor		::type_id::create("m_monitor", this);

		if (get_is_active() == UVM_ACTIVE) begin
			m_driver	= dsi3_slave_driver   ::type_id::create("m_driver", this);
			m_sequencer	= dsi3_slave_sequencer::type_id::create("m_sequencer", this);
		end
		
		`include "includes/dsi3_slave_agent_append_to_build_phase.sv"

	endfunction

	function void connect_phase(uvm_phase phase);
		if (m_config.vif == null)
			`uvm_warning(get_type_name(), "dsi3_slave virtual interface is not set!")

		m_monitor.vif		= m_config.vif;
		m_monitor.m_config	= m_config;
		m_monitor.analysis_port.connect(analysis_port);

		if (get_is_active() == UVM_ACTIVE) begin
			m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
			m_driver.vif			= m_config.vif;
			m_driver.m_config		= m_config;
			m_sequencer.m_config	= m_config;
		end

		`include "includes/dsi3_slave_agent_append_to_connect_phase.sv"

	endfunction

	function uvm_active_passive_enum get_is_active();
		if (m_is_active == -1) begin
			if (uvm_config_db#(uvm_bitstream_t)::get(this, "", "is_active", m_is_active)) begin
				if (m_is_active != int'(m_config.is_active))
					`uvm_warning(get_type_name(), "is_active field in config_db conflicts with config object")
			end
			else 
				m_is_active = m_config.is_active;
		end
		return uvm_active_passive_enum'(m_is_active);
	endfunction

	`include "includes/dsi3_slave_agent_inc_inside_class.sv"

endclass 

// You can insert code here by setting agent_inc_after_class in file dsi3_slave.tpl

`endif

