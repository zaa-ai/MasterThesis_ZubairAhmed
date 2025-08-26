//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef DIGITAL_SIGNAL_SEQ_ITEM_SV
`define DIGITAL_SIGNAL_SEQ_ITEM_SV

`include "includes/digital_signal_trans_inc_before_class.sv"

class digital_signal_tr extends uvm_sequence_item; 

	`uvm_object_utils(digital_signal_tr)

	// To include variables in copy, compare, print, record, pack, unpack, and compare2string, define them using trans_var in file digital_signal.tpl
	// To exclude variables from compare, pack, and unpack methods, define them using trans_meta in file digital_signal.tpl

	// Transaction variables
	logic					value;
	rand digital_signal_t	_val;
	
	function new(string name = "");
		super.new(name);
	endfunction	
	
	// You can remove do_copy/compare/print/record and convert2string method by setting trans_generate_methods_inside_class = no in file spi.tpl
	virtual function void do_copy(uvm_object rhs);
		digital_signal_tr rhs_;
		if (!$cast(rhs_, rhs)) `uvm_fatal(get_type_name(), "Cast of rhs object failed")
		super.do_copy(rhs);
		_val = rhs_._val;
		value = rhs_.value;
	endfunction
	
	virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
		bit result;
		digital_signal_tr rhs_;
		if (!$cast(rhs_, rhs)) `uvm_fatal(get_type_name(), "Cast of rhs object failed")
		result = super.do_compare(rhs, comparer);
		result &= comparer.compare_field("_val",	_val,	rhs_._val,	$bits(_val)); 
		result &= comparer.compare_field("value",	value,	rhs_.value,	$bits(value)); 
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
		`uvm_record_field("_val",	_val ) 
		`uvm_record_field("value",	value ) 
	endfunction
		
	virtual function void do_pack(uvm_packer packer);
		super.do_pack(packer);
			`uvm_pack_enum(_val)
			`uvm_pack_int(value)
	endfunction
	
	virtual function void do_unpack(uvm_packer packer);
		super.do_unpack(packer);
			`uvm_unpack_enum(_val, digital_signal_t)
			`uvm_unpack_int(value)
	endfunction
	
	virtual function string convert2string();
		string s;
		$sformat(s, "%s\n", super.convert2string());
		$sformat(s, {"%s\n",
			"_val = %s" ,
			"value = 'h%0h  'd%0d" },
			get_full_name() , _val.name, value, value); 
		return s;
	endfunction

	`include "includes/digital_signal_trans_inc_inside_class.sv"

endclass

// You can insert code here by setting trans_inc_after_class in file digital_signal.tpl

`endif // SPI_SEQ_ITEM_SV
