//-----------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author     : Eugene - Easy UVM Generator
//
// Description: This file has been generated automatically by Eugene
//				This file should not be modified manually. 
//-----------------------------------------------------------------------------
`ifndef ELIP_BUS_SEQ_ITEM_SV
`define ELIP_BUS_SEQ_ITEM_SV

// You can insert code here by setting trans_inc_before_class in file elip_bus.tpl

class elip_tr extends uvm_sequence_item; 

	`uvm_object_utils(elip_tr)

	// To include variables in copy, compare, print, record, pack, unpack, and compare2string, define them using trans_var in file elip_bus.tpl
	// To exclude variables from compare, pack, and unpack methods, define them using trans_meta in file elip_bus.tpl

	// Transaction variables
	rand logic[15:0]	address;
	logic[15:0]	data_read;
	logic[5:0]     data_read_ecc;
	rand logic[15:0]	data_write;
	rand logic[5:0]     data_write_ecc;
	rand bit			write;
	
	function new(string name = "");
		super.new(name);
	endfunction	
	
	// You can remove do_copy/compare/print/record and convert2string method by setting trans_generate_methods_inside_class = no in file spi.tpl
	virtual function void do_copy(uvm_object rhs);
		elip_tr rhs_;
		if (!$cast(rhs_, rhs)) `uvm_fatal(get_type_name(), "Cast of rhs object failed")
		super.do_copy(rhs);
		address = rhs_.address;
		data_read = rhs_.data_read;
		data_read_ecc = rhs_.data_read_ecc;
		data_write = rhs_.data_write;
		data_write_ecc = rhs_.data_write_ecc;
		write = rhs_.write;
	endfunction
	
	virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
		bit result;
		elip_tr rhs_;
		if (!$cast(rhs_, rhs)) `uvm_fatal(get_type_name(), "Cast of rhs object failed")
		result = super.do_compare(rhs, comparer);
		result &= comparer.compare_field("address",	address,	rhs_.address,	$bits(address)); 
		result &= comparer.compare_field("data_read",	data_read,	rhs_.data_read,	$bits(data_read)); 
		result &= comparer.compare_field("data_read_ecc",	data_read_ecc,	rhs_.data_read_ecc,	$bits(data_read_ecc)); 
		result &= comparer.compare_field("data_write",	data_write,	rhs_.data_write,	$bits(data_write)); 
		result &= comparer.compare_field("data_write_ecc",	data_write_ecc,	rhs_.data_write_ecc,	$bits(data_write_ecc)); 
		result &= comparer.compare_field("write",	write,	rhs_.write,	$bits(write)); 
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
		`uvm_record_field("address",	address ) 
		`uvm_record_field("data_read",	data_read ) 
		`uvm_record_field("data_read_ecc",	data_read_ecc ) 
		`uvm_record_field("data_write",	data_write ) 
		`uvm_record_field("data_write_ecc",	data_write_ecc ) 
		`uvm_record_field("write",	write ) 
	endfunction
		
	virtual function void do_pack(uvm_packer packer);
		super.do_pack(packer);
			`uvm_pack_int(address)
			`uvm_pack_int(data_read)
			`uvm_pack_int(data_read_ecc)
			`uvm_pack_int(data_write)
			`uvm_pack_int(data_write_ecc)
			`uvm_pack_int(write)
	endfunction
	
	virtual function void do_unpack(uvm_packer packer);
		super.do_unpack(packer);
			`uvm_unpack_int(address)
			`uvm_unpack_int(data_read)
			`uvm_unpack_int(data_read_ecc)
			`uvm_unpack_int(data_write)
			`uvm_unpack_int(data_write_ecc)
			`uvm_unpack_int(write)
	endfunction
	
	virtual function string convert2string();
		string s;
		$sformat(s, "%s\n", super.convert2string());
		$sformat(s, {"%s\n",
			"address = 'h%0h  'd%0d" ,
			"data_read = 'h%0h  'd%0d" ,
			"data_read_ecc = 'h%0h  'd%0d" ,
			"data_write = 'h%0h  'd%0d" ,
			"data_write_ecc = 'h%0h  'd%0d" ,
			"write = 'h%0h  'd%0d" },
			get_full_name() , address, address, data_read, data_read, data_read_ecc, data_read_ecc, data_write, data_write, data_write_ecc, data_write_ecc, write, write); 
		return s;
	endfunction

	// You can insert code here by setting trans_inc_inside_class in file elip_bus.tpl

endclass

// You can insert code here by setting trans_inc_after_class in file elip_bus.tpl

`endif // SPI_SEQ_ITEM_SV
