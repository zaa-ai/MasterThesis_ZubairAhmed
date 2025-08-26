//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef JTAG_MASTER_COVERAGE_SV
`define JTAG_MASTER_COVERAGE_SV

// You can insert code here by setting agent_cover_inc_before_class in file jtag_master.tpl

class jtag_master_coverage extends uvm_subscriber #(jtag_tr);

	`uvm_component_utils(jtag_master_coverage)
	
	jtag_master_config m_config;
	bit        m_is_covered;
	jtag_tr m_item;
	
		// You can replace covergroup m_cov by setting agent_cover_inc in file jtag_master.tpl
		// or remove covergroup m_cov by setting agent_cover_generate_methods_inside_class = no in file jtag_master.tpl
		covergroup m_cov;
			option.per_instance = 1;
				cp_ir_length: coverpoint m_item.ir_length;
				cp_dr_length: coverpoint m_item.dr_length;
				cp_ir_value: coverpoint m_item.ir_value;
				cp_dr_value: coverpoint m_item.dr_value;
				cp_init_jtag: coverpoint m_item.init_jtag;
				cp_read_dr: coverpoint m_item.read_dr;
				cp_read_ir: coverpoint m_item.read_ir;
		endgroup
	
	function new(string name, uvm_component parent);
		super.new(name, parent);
		m_is_covered = 0;
		m_cov = new();
	endfunction
	
	function void write(input jtag_tr t);
		if (m_config.coverage_enable) begin
			m_item = t;
			m_cov.sample();
			if (int'(m_cov.get_inst_coverage()) >= m_cov.option.goal) m_is_covered = 1;
		end
	endfunction
	
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		if (!uvm_config_db #(jtag_master_config)::get(this, "", "config", m_config)) begin
			`uvm_error(get_type_name(), "jtag_master config not found")
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
	
	// You can insert code here by setting agent_cover_inc_inside_class in file jtag_master.tpl

endclass 

// You can insert code here by setting agent_cover_inc_after_class in file jtag_master.tpl

`endif

