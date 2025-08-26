//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef ELIP_BUS_COVERAGE_SV
`define ELIP_BUS_COVERAGE_SV

// You can insert code here by setting agent_cover_inc_before_class in file elip_bus.tpl

class elip_bus_coverage extends uvm_subscriber #(elip_tr);

	`uvm_component_utils(elip_bus_coverage)
	
	elip_bus_config m_config;
	bit        m_is_covered;
	elip_tr m_item;
	
		// You can replace covergroup m_cov by setting agent_cover_inc in file elip_bus.tpl
		// or remove covergroup m_cov by setting agent_cover_generate_methods_inside_class = no in file elip_bus.tpl
		covergroup m_cov;
			option.per_instance = 1;
				cp_address: coverpoint m_item.address;
				cp_data_read: coverpoint m_item.data_read;
				cp_data_read_ecc: coverpoint m_item.data_read_ecc;
				cp_data_write: coverpoint m_item.data_write;
				cp_data_write_ecc: coverpoint m_item.data_write_ecc;
				cp_write: coverpoint m_item.write;
		endgroup
	
	function new(string name, uvm_component parent);
		super.new(name, parent);
		m_is_covered = 0;
		m_cov = new();
	endfunction
	
	function void write(input elip_tr t);
		if (m_config.coverage_enable) begin
			m_item = t;
			m_cov.sample();
			if (int'(m_cov.get_inst_coverage()) >= m_cov.option.goal) m_is_covered = 1;
		end
	endfunction
	
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		if (!uvm_config_db #(elip_bus_config)::get(this, "", "config", m_config)) begin
			`uvm_error(get_type_name(), "elip_bus config not found")
		end
	endfunction
	
	function void report_phase(uvm_phase phase);
		if (m_config.coverage_enable) begin
			`uvm_info(get_type_name(), $sformatf("Coverage score = %3.1f%%", m_cov.get_inst_coverage()), UVM_MEDIUM)
		end
		else begin
			`uvm_info(get_type_name(), "Coverage disabled for this agent", UVM_MEDIUM)
		end
	endfunction
	
	// You can insert code here by setting agent_cover_inc_inside_class in file elip_bus.tpl

endclass 

// You can insert code here by setting agent_cover_inc_after_class in file elip_bus.tpl

`endif

