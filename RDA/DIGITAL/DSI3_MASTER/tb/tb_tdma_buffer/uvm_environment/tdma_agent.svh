`ifndef TDMA_AGENT_SV
`define TDMA_AGENT_SV

class tdma_agent extends uvm_agent;

	`uvm_component_utils(tdma_agent)

	tdma_config		m_config;
	tdma_sequencer	m_sequencer;
	tdma_driver		m_driver;

	local int m_is_active = -1;

	function	new(string name, uvm_component parent);
		super.new(name, parent);
	endfunction

	
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);

		if (!uvm_config_db #(tdma_config)::get(this, "", "config", m_config))
			`uvm_error(get_type_name(), "tdma config not found")


		if (get_is_active() == UVM_ACTIVE) begin
			m_driver	= tdma_driver   ::type_id::create("m_driver", this);
			m_sequencer	= tdma_sequencer::type_id::create("m_sequencer", this);
		end
		
//		`include "tdma_agent_append_to_build_phase.svh"

	endfunction

	function void connect_phase(uvm_phase phase);
		if (m_config.vif == null)
			`uvm_warning(get_type_name(), "tdma virtual interface is not set!")

		if (get_is_active() == UVM_ACTIVE) begin
			m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
			m_driver.vif		= m_config.vif;
			m_driver.m_config	= m_config;
		end

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

endclass 

`endif
