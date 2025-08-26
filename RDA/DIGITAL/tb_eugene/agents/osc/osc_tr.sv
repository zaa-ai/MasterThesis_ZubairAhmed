//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef OSC_SEQ_ITEM_SV
`define OSC_SEQ_ITEM_SV

// You can insert code here by setting trans_inc_before_class in file osc.tpl

class osc_tr extends uvm_sequence_item; 

	`uvm_object_utils(osc_tr)

	// To include variables in copy, compare, print, record, pack, unpack, and compare2string, define them using trans_var in file osc.tpl
	// To exclude variables from compare, pack, and unpack methods, define them using trans_meta in file osc.tpl

	// Transaction variables
	rand	integer	freq;
	rand	bit		enabled;
	
	function new(string name = "");
		super.new(name);
	endfunction	
	
	// You can remove do_copy/compare/print/record and convert2string method by setting trans_generate_methods_inside_class = no in file spi.tpl
	virtual function void do_copy(uvm_object rhs);
		osc_tr rhs_;
		if (!$cast(rhs_, rhs)) `uvm_fatal(get_type_name(), "Cast of rhs object failed")
		super.do_copy(rhs);
		freq = rhs_.freq;
		enabled = rhs_.enabled;
	endfunction
	
	virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
		bit result;
		osc_tr rhs_;
		if (!$cast(rhs_, rhs)) `uvm_fatal(get_type_name(), "Cast of rhs object failed")
		result = super.do_compare(rhs, comparer);
		result &= comparer.compare_field("freq",	freq,	rhs_.freq,	$bits(freq)); 
		result &= comparer.compare_field("enabled",	enabled,	rhs_.enabled,	$bits(enabled)); 
		return result;
	endfunction
	
	virtual function void do_print(uvm_printer printer);
		if (printer.knobs.sprint == 0)
			`uvm_info(get_type_name(), convert2string(), UVM_MEDIUM)
		else
			printer.m_string = convert2string();
	endfunction
	
	virtual function void do_record(uvm_recorder recorder); //TODO: add special recording for ints or strings...
		super.do_record(recorder);
		`uvm_record_field("freq",	freq ) 
		`uvm_record_field("enabled",	enabled ) 
	endfunction
		
	virtual function void do_pack(uvm_packer packer);
		super.do_pack(packer);
			`uvm_pack_int(freq)
			`uvm_pack_int(enabled)
	endfunction
	
	virtual function void do_unpack(uvm_packer packer);
		super.do_unpack(packer);
			`uvm_unpack_int(freq)
			`uvm_unpack_int(enabled)
	endfunction
	
	virtual function string convert2string();
		string s;
		$sformat(s, "%s\n", super.convert2string());
		$sformat(s, {"%s\n",
			"freq = 'h%0h  'd%0d" ,
			"enabled = 'h%0h  'd%0d" },
			get_full_name() , freq, freq, enabled, enabled); 
		return s;
	endfunction

	// You can insert code here by setting trans_inc_inside_class in file osc.tpl

endclass

// You can insert code here by setting trans_inc_after_class in file osc.tpl

`endif // SPI_SEQ_ITEM_SV
