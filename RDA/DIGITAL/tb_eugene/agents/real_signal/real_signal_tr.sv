//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef REAL_SIGNAL_SEQ_ITEM_SV
`define REAL_SIGNAL_SEQ_ITEM_SV

// You can insert code here by setting trans_inc_before_class in file real_signal.tpl

class real_signal_tr extends uvm_sequence_item; 

	`uvm_object_utils(real_signal_tr)

	// To include variables in copy, compare, print, record, pack, unpack, and compare2string, define them using trans_var in file real_signal.tpl
	// To exclude variables from compare, pack, and unpack methods, define them using trans_meta in file real_signal.tpl

	// Transaction variables
	rand longint value;
	rand longint duration;
	rand longint edge_duration;
	
	function new(string name = "");
		super.new(name);
	endfunction	
	
	// You can remove do_copy/compare/print/record and convert2string method by setting trans_generate_methods_inside_class = no in file spi.tpl
	virtual function void do_copy(uvm_object rhs);
		real_signal_tr rhs_;
		if (!$cast(rhs_, rhs)) `uvm_fatal(get_type_name(), "Cast of rhs object failed")
		super.do_copy(rhs);
		value = rhs_.value;
		duration = rhs_.duration;
		edge_duration = rhs_.edge_duration;
	endfunction
	
	virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
		bit result;
		real_signal_tr rhs_;
		if (!$cast(rhs_, rhs)) `uvm_fatal(get_type_name(), "Cast of rhs object failed")
		result = super.do_compare(rhs, comparer);
		result &= comparer.compare_field("value",	value,	rhs_.value,	$bits(value)); 
		result &= comparer.compare_field("duration",	duration,	rhs_.duration,	$bits(duration)); 
		result &= comparer.compare_field("edge_duration",	edge_duration,	rhs_.edge_duration,	$bits(edge_duration)); 
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
		`uvm_record_field("value",	value ) 
		`uvm_record_field("duration",	duration ) 
		`uvm_record_field("edge_duration",	edge_duration ) 
	endfunction
		
	virtual function void do_pack(uvm_packer packer);
		super.do_pack(packer);
			`uvm_pack_int(value)
			`uvm_pack_int(duration)
			`uvm_pack_int(edge_duration)
	endfunction
	
	virtual function void do_unpack(uvm_packer packer);
		super.do_unpack(packer);
			`uvm_unpack_int(value)
			`uvm_unpack_int(duration)
			`uvm_unpack_int(edge_duration)
	endfunction
	
	virtual function string convert2string();
		string s;
		$sformat(s, "%s\n", super.convert2string());
		$sformat(s, {"%s\n",
			"value = 'h%0h  'd%0d" ,
			"duration = 'h%0h  'd%0d" ,
			"edge_duration = 'h%0h  'd%0d" },
			get_full_name() , value, value, duration, duration, edge_duration, edge_duration); 
		return s;
	endfunction

	// You can insert code here by setting trans_inc_inside_class in file real_signal.tpl

endclass

// You can insert code here by setting trans_inc_after_class in file real_signal.tpl

`endif // SPI_SEQ_ITEM_SV
