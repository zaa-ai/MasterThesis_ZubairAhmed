function void do_copy(uvm_object rhs);
	jtag_tr rhs_;
	if (!$cast(rhs_, rhs))
		`uvm_fatal(get_type_name(), "Cast of rhs object failed")
	super.do_copy(rhs);
	ir_length = rhs_.ir_length;
	dr_length = rhs_.dr_length;
	ir_value  = rhs_.ir_value; 
	dr_value  = rhs_.dr_value; 
	init_jtag = rhs_.init_jtag;
	read_dr   = rhs_.read_dr;  
	read_ir   = rhs_.read_ir;  
endfunction : do_copy


function bit do_compare(uvm_object rhs, uvm_comparer comparer);
	bit result;
	jtag_tr rhs_;
	if (!$cast(rhs_, rhs))
		`uvm_fatal(get_type_name(), "Cast of rhs object failed")
	result = super.do_compare(rhs, comparer);
	result &= comparer.compare_field("ir_length", ir_length, rhs_.ir_length, $bits(ir_length));
	result &= comparer.compare_field("dr_length", dr_length, rhs_.dr_length, $bits(dr_length));
	result &= comparer.compare_field("ir_value", ir_value,   rhs_.ir_value,  $bits(ir_value));
	result &= comparer.compare_field("dr_value", dr_value,   rhs_.dr_value,  $bits(dr_value));
	result &= comparer.compare_field("init_jtag", init_jtag, rhs_.init_jtag, $bits(init_jtag));
	result &= comparer.compare_field("read_dr", read_dr,     rhs_.read_dr,   $bits(read_dr));
	result &= comparer.compare_field("read_ir", read_ir,     rhs_.read_ir,   $bits(read_ir));
	return result;
endfunction : do_compare


function void do_print(uvm_printer printer);
	if (printer.knobs.sprint == 0)
		`uvm_info(get_type_name(), convert2string(), UVM_MEDIUM)
	else
		printer.m_string = convert2string();
endfunction : do_print


function void do_record(uvm_recorder recorder);
	super.do_record(recorder);
	`uvm_record_field("IR_length", ir_length)
	`uvm_record_field("IR in    ", $sformatf("%4h", ir_value))
	`uvm_record_field("IR out   ", $sformatf("%4h", read_ir ))
	`uvm_record_field("DR length", dr_length)
	`uvm_record_field("DR in    ", $sformatf("%4h (%5d)", dr_value, dr_value) )
	`uvm_record_field("DR out   ", $sformatf("%4h (%5d)", read_dr, read_dr) )
	`uvm_record_field("init     ", init_jtag)
endfunction : do_record


function void do_pack(uvm_packer packer);
	super.do_pack(packer);
	`uvm_pack_int(ir_length) 
	`uvm_pack_int(dr_length) 
	`uvm_pack_int(ir_value)  
	`uvm_pack_int(dr_value)  
	`uvm_pack_int(init_jtag) 
	`uvm_pack_int(read_dr)   
	`uvm_pack_int(read_ir)   
endfunction : do_pack


function void do_unpack(uvm_packer packer);
	super.do_unpack(packer);
	`uvm_unpack_int(ir_length) 
	`uvm_unpack_int(dr_length) 
	`uvm_unpack_int(ir_value)  
	`uvm_unpack_int(dr_value)  
	`uvm_unpack_int(init_jtag) 
	`uvm_unpack_int(read_dr)   
	`uvm_unpack_int(read_ir)   
endfunction : do_unpack


function string convert2string();
	string s;
	$sformat(s, "%s\n", super.convert2string());
	$sformat(s, {"%s\n",
				"ir_length = 'h%0h  'd%0d\n", 
				"dr_length = 'h%0h  'd%0d\n", 
				"ir_value  = 'h%0h  'd%0d\n", 
				"dr_value  = 'h%0h  'd%0d\n", 
				"init_jtag = 'h%0h  'd%0d\n", 
				"read_dr   = 'h%0h  'd%0d\n", 
				"read_ir   = 'h%0h  'd%0d\n"},
			get_full_name(), ir_length, ir_length, dr_length, dr_length, ir_value, ir_value, dr_value, dr_value, init_jtag, init_jtag, read_dr, read_dr, read_ir, read_ir);
	return s;
endfunction : convert2string
