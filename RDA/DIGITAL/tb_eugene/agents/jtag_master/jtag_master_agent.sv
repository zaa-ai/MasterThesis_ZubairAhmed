//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef JTAG_MASTER_AGENT_SV
`define JTAG_MASTER_AGENT_SV

// You can insert code here by setting agent_inc_before_class in file jtag_master.tpl

class jtag_master_agent extends uvm_agent;

	`uvm_component_utils(jtag_master_agent)

	uvm_analysis_port #(jtag_tr) analysis_port;

	jtag_master_config	m_config;
	jtag_master_sequencer	m_sequencer;
	jtag_master_driver	m_driver;
	jtag_master_monitor	m_monitor;

	local int m_is_active = -1;

	function	new(string name, uvm_component parent);
		super.new(name, parent);
		analysis_port = new("analysis_port", this);
	endfunction

	// You can remove build/connect_phase and get_is_active by setting agent_generate_methods_after_class = no in file jtag_master.tpl
	
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		
		// You can insert code here by setting agent_prepend_to_build_phase in file jtag_master.tpl

		if (!uvm_config_db #(jtag_master_config)::get(this, "", "config", m_config))
			`uvm_error(get_type_name(), "jtag_master config not found")

		m_monitor	= jtag_master_monitor		::type_id::create("m_monitor", this);

		if (get_is_active() == UVM_ACTIVE) begin
			m_driver	= jtag_master_driver   ::type_id::create("m_driver", this);
			m_sequencer	= jtag_master_sequencer::type_id::create("m_sequencer", this);
		end
		
		// You can insert code here by setting agent_append_to_build_phase in file jtag_master.tpl

	endfunction

	function void connect_phase(uvm_phase phase);
		if (m_config.vif == null)
			`uvm_warning(get_type_name(), "jtag_master virtual interface is not set!")

		m_monitor.vif		= m_config.vif;
		m_monitor.m_config	= m_config;
		m_monitor.analysis_port.connect(analysis_port);

		if (get_is_active() == UVM_ACTIVE) begin
			m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
			m_driver.vif			= m_config.vif;
			m_driver.m_config		= m_config;
			m_sequencer.m_config	= m_config;
		end

		// You can insert code here by setting agent_append_to_connect_phase in file jtag_master.tpl

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

	// You can insert code here by setting agent_inc_inside_class in file jtag_master.tpl

endclass 

// You can insert code here by setting agent_inc_after_class in file jtag_master.tpl

`endif

