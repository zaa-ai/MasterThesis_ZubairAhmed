//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef BUFFER_WRITER_COVERAGE_SV
`define BUFFER_WRITER_COVERAGE_SV

// You can insert code here by setting agent_cover_inc_before_class in file buffer_writer.tpl

class buffer_writer_coverage extends uvm_subscriber #(buffer_writer_tr);

	`uvm_component_utils(buffer_writer_coverage)
	
	buffer_writer_config m_config;
	bit        m_is_covered;
	buffer_writer_tr m_item;
	
		// You can replace covergroup m_cov by setting agent_cover_inc in file buffer_writer.tpl
		// or remove covergroup m_cov by setting agent_cover_generate_methods_inside_class = no in file buffer_writer.tpl
		covergroup m_cov;
			option.per_instance = 1;
				cp_action: coverpoint m_item.action;
				cp_data: coverpoint m_item.data;
				cp_ecc: coverpoint m_item.ecc;
				cp_full: coverpoint m_item.full;
				cp_nearly_full: coverpoint m_item.nearly_full;
		endgroup
	
	function new(string name, uvm_component parent);
		super.new(name, parent);
		m_is_covered = 0;
		m_cov = new();
	endfunction
	
	function void write(input buffer_writer_tr t);
		if (m_config.coverage_enable) begin
			m_item = t;
			m_cov.sample();
			if (int'(m_cov.get_inst_coverage()) >= m_cov.option.goal) m_is_covered = 1;
		end
	endfunction
	
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		if (!uvm_config_db #(buffer_writer_config)::get(this, "", "config", m_config)) begin
			`uvm_error(get_type_name(), "buffer_writer config not found")
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
	
	// You can insert code here by setting agent_cover_inc_inside_class in file buffer_writer.tpl

endclass 

// You can insert code here by setting agent_cover_inc_after_class in file buffer_writer.tpl

`endif

