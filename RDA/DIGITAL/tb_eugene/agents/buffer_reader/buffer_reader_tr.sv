//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef BUFFER_READER_SEQ_ITEM_SV
`define BUFFER_READER_SEQ_ITEM_SV

`include "includes/buffer_reader_trans_inc_before_class.sv"

class buffer_reader_tr extends uvm_sequence_item; 

	`uvm_object_utils(buffer_reader_tr)

	// To include variables in copy, compare, print, record, pack, unpack, and compare2string, define them using trans_var in file buffer_reader.tpl
	// To exclude variables from compare, pack, and unpack methods, define them using trans_meta in file buffer_reader.tpl

	// Transaction variables
	rand logic[15:0]	data;
	rand logic[5:0]		ecc;
	bit			empty;
	rand buffer_reader_action_e	action;
	
	function new(string name = "");
		super.new(name);
	endfunction	
	
	// You can remove do_copy/compare/print/record and convert2string method by setting trans_generate_methods_inside_class = no in file spi.tpl
	virtual function void do_copy(uvm_object rhs);
		buffer_reader_tr rhs_;
		if (!$cast(rhs_, rhs)) `uvm_fatal(get_type_name(), "Cast of rhs object failed")
		super.do_copy(rhs);
		action = rhs_.action;
		data = rhs_.data;
		ecc = rhs_.ecc;
		empty = rhs_.empty;
	endfunction
	
	virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
		bit result;
		buffer_reader_tr rhs_;
		if (!$cast(rhs_, rhs)) `uvm_fatal(get_type_name(), "Cast of rhs object failed")
		result = super.do_compare(rhs, comparer);
		result &= comparer.compare_field("action",	action,	rhs_.action,	$bits(action)); 
		result &= comparer.compare_field("data",	data,	rhs_.data,	$bits(data)); 
		result &= comparer.compare_field("ecc",	ecc,	rhs_.ecc,	$bits(ecc)); 
		result &= comparer.compare_field("empty",	empty,	rhs_.empty,	$bits(empty)); 
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
		`uvm_record_field("action",	action ) 
		`uvm_record_field("data",	data ) 
		`uvm_record_field("ecc",	ecc ) 
		`uvm_record_field("empty",	empty ) 
	endfunction
		
	virtual function void do_pack(uvm_packer packer);
		super.do_pack(packer);
			`uvm_pack_enum(action)
			`uvm_pack_int(data)
			`uvm_pack_int(ecc)
			`uvm_pack_int(empty)
	endfunction
	
	virtual function void do_unpack(uvm_packer packer);
		super.do_unpack(packer);
			`uvm_unpack_enum(action, buffer_reader_action_e)
			`uvm_unpack_int(data)
			`uvm_unpack_int(ecc)
			`uvm_unpack_int(empty)
	endfunction
	
	virtual function string convert2string();
		string s;
		$sformat(s, "%s\n", super.convert2string());
		$sformat(s, {"%s\n",
			"action = %s" ,
			"data = 'h%0h  'd%0d" ,
			"ecc = 'h%0h  'd%0d" ,
			"empty = 'h%0h  'd%0d" },
			get_full_name() , action.name, data, data, ecc, ecc, empty, empty); 
		return s;
	endfunction

	// You can insert code here by setting trans_inc_inside_class in file buffer_reader.tpl

endclass

// You can insert code here by setting trans_inc_after_class in file buffer_reader.tpl

`endif // SPI_SEQ_ITEM_SV
