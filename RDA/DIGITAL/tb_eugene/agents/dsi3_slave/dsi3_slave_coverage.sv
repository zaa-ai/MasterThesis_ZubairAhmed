//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef DSI3_SLAVE_COVERAGE_SV
`define DSI3_SLAVE_COVERAGE_SV

// You can insert code here by setting agent_cover_inc_before_class in file dsi3_slave.tpl

class dsi3_slave_coverage extends uvm_subscriber #(dsi3_slave_tr);

	`uvm_component_utils(dsi3_slave_coverage)
	
	dsi3_slave_config m_config;
	bit        m_is_covered;
	dsi3_slave_tr m_item;
	
		// You can replace covergroup m_cov by setting agent_cover_inc in file dsi3_slave.tpl
		// or remove covergroup m_cov by setting agent_cover_generate_methods_inside_class = no in file dsi3_slave.tpl
		covergroup m_cov;
			option.per_instance = 1;
				cp_tolerance_int: coverpoint m_item.tolerance_int;
				cp_chiptime: coverpoint m_item.chiptime;
				cp_chips_per_symbol: coverpoint m_item.chips_per_symbol;
				cp_msg_type: coverpoint m_item.msg_type;
				cp_symbol_coding_error_injection: coverpoint m_item.symbol_coding_error_injection;
				cp_chip_length_error_injection: coverpoint m_item.chip_length_error_injection;
				cp_symbol_coding_error: coverpoint m_item.symbol_coding_error;
		endgroup
	
	function new(string name, uvm_component parent);
		super.new(name, parent);
		m_is_covered = 0;
		m_cov = new();
	endfunction
	
	function void write(input dsi3_slave_tr t);
		if (m_config.coverage_enable) begin
			m_item = t;
			m_cov.sample();
			if (int'(m_cov.get_inst_coverage()) >= m_cov.option.goal) m_is_covered = 1;
		end
	endfunction
	
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		if (!uvm_config_db #(dsi3_slave_config)::get(this, "", "config", m_config)) begin
			`uvm_error(get_type_name(), "dsi3_slave config not found")
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
	
	// You can insert code here by setting agent_cover_inc_inside_class in file dsi3_slave.tpl

endclass 

`include "includes/dsi3_slave_agent_cover_inc_after_class.sv"

`endif

