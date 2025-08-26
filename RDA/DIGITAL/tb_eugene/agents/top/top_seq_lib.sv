//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------

`ifndef TOP_SEQ_LIB_SV
`define TOP_SEQ_LIB_SV

class top_default_seq extends uvm_sequence #(uvm_sequence_item);

	`uvm_object_utils(top_default_seq)
	
	uvm_status_e status;

	ral_sys_device_registers regmodel;
	ral_sys_jtag_test_registers test_regmodel;
	top_config m_config;

	jtag_master_agent m_jtag_master_agent;
	spi_agent m_spi_agent;
	dsi3_master_agent m_dsi3_master_agent[1:0];
	dsi3_slave_agent m_dsi3_slave_agent[1:0];
	digital_signal_agent m_tmode_agent;
	digital_signal_agent m_resb_agent;
	digital_signal_agent m_rfc_agent;
	digital_signal_agent m_bfwb_agent;
	digital_signal_agent m_dab_agent;
	digital_signal_agent m_intb_agent;
	digital_signal_agent m_syncb_agent;
	digital_signal_agent m_syncb_out_agent;
	osc_agent m_osc_agent;
	real_signal_agent m_iload_agent[1:0];
	real_signal_agent m_vsup_agent;
	real_signal_agent m_vcc_agent;
	real_signal_agent m_vdd18_agent;
	real_signal_agent m_aout_agent;
	real_signal_agent m_ldo_agent;
	real_signal_agent m_temp_agent;

	virtual jtag_master_if jtag_master;
	virtual spi_if spi;
	virtual dsi3_slave_if dsi3_slave[1:0];
	virtual digital_signal_if tmode;
	virtual digital_signal_if resb;
	virtual digital_signal_if rfc;
	virtual digital_signal_if bfwb;
	virtual digital_signal_if dab;
	virtual digital_signal_if intb;
	virtual digital_signal_if syncb;
	virtual digital_signal_if syncb_out;
	virtual osc_if osc;
	virtual real_signal_if iload[1:0];
	virtual real_signal_if vsup;
	virtual real_signal_if vcc;
	virtual real_signal_if vdd18;
	virtual real_signal_if aout;
	virtual real_signal_if ldo;
	virtual real_signal_if temp;

	function new(string name = "");
		super.new(name);
	endfunction : new
  
	virtual task body();
		`uvm_fatal(get_type_name(), "top_default_seq must always be replaced by a used defined test sequence")
	endtask : body

	virtual task pre_start();
		uvm_phase phase = get_starting_phase();
		if (phase != null) begin
			phase.raise_objection(this);
		end
		if(m_parent_sequence != null) begin
			top_default_seq parent;
			if($cast(parent, m_parent_sequence) == 1) begin
				copy_references_from(parent);	
			end
		end
	endtask: pre_start
	
	virtual function void copy_references_from(top_default_seq source_seq);

		regmodel = source_seq.regmodel;
		test_regmodel = source_seq.test_regmodel;
		m_config = source_seq.m_config;

		m_jtag_master_agent = source_seq.m_jtag_master_agent;
		m_spi_agent = source_seq.m_spi_agent;
		m_dsi3_master_agent = source_seq.m_dsi3_master_agent;
		m_dsi3_slave_agent = source_seq.m_dsi3_slave_agent;
		m_tmode_agent = source_seq.m_tmode_agent;
		m_resb_agent = source_seq.m_resb_agent;
		m_rfc_agent = source_seq.m_rfc_agent;
		m_bfwb_agent = source_seq.m_bfwb_agent;
		m_dab_agent = source_seq.m_dab_agent;
		m_intb_agent = source_seq.m_intb_agent;
		m_syncb_agent = source_seq.m_syncb_agent;
		m_syncb_out_agent = source_seq.m_syncb_out_agent;
		m_osc_agent = source_seq.m_osc_agent;
		m_iload_agent = source_seq.m_iload_agent;
		m_vsup_agent = source_seq.m_vsup_agent;
		m_vcc_agent = source_seq.m_vcc_agent;
		m_vdd18_agent = source_seq.m_vdd18_agent;
		m_aout_agent = source_seq.m_aout_agent;
		m_ldo_agent = source_seq.m_ldo_agent;
		m_temp_agent = source_seq.m_temp_agent;

		jtag_master = source_seq.jtag_master;
		spi = source_seq.spi;
		dsi3_slave = source_seq.dsi3_slave;
		tmode = source_seq.tmode;
		resb = source_seq.resb;
		rfc = source_seq.rfc;
		bfwb = source_seq.bfwb;
		dab = source_seq.dab;
		intb = source_seq.intb;
		syncb = source_seq.syncb;
		syncb_out = source_seq.syncb_out;
		osc = source_seq.osc;
		iload = source_seq.iload;
		vsup = source_seq.vsup;
		vcc = source_seq.vcc;
		vdd18 = source_seq.vdd18;
		aout = source_seq.aout;
		ldo = source_seq.ldo;
		temp = source_seq.temp;
	endfunction

	virtual task post_start();
		uvm_phase phase = get_starting_phase();
		if (phase != null) begin 
			phase.drop_objection(this);
		end
	endtask: post_start

endclass : top_default_seq

`include "includes/top_seq_inc.sv"

`endif // TOP_SEQ_LIB_SV