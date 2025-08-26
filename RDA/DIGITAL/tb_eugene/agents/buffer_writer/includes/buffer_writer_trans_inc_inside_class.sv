function void do_copy(uvm_object rhs);
	buffer_writer_tr rhs_;
	if (!$cast(rhs_, rhs))
		`uvm_fatal(get_type_name(), "Cast of rhs object failed")
	super.do_copy(rhs);
	action      = rhs_.action;     
	data        = rhs_.data;       
	full        = rhs_.full;       
	nearly_full = rhs_.nearly_full;
endfunction : do_copy


function bit do_compare(uvm_object rhs, uvm_comparer comparer);
	bit result;
	buffer_writer_tr rhs_;
	if (!$cast(rhs_, rhs))
		`uvm_fatal(get_type_name(), "Cast of rhs object failed")
	result = super.do_compare(rhs, comparer);
	result &= comparer.compare_field("action", action,           rhs_.action,      $bits(action));
	if ((action == BUFFER_WRITE) || (action == BUFFER_WRITE_FIRST)) begin
		result &= comparer.compare_field("data", data,               rhs_.data,        $bits(data));
		result &= comparer.compare_field("ecc", ecc,               rhs_.ecc,        $bits(data));
	end
//	result &= comparer.compare_field("full", full,               rhs_.full,        $bits(full));
//	result &= comparer.compare_field("nearly_full", nearly_full, rhs_.nearly_full, $bits(nearly_full));
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
	// Use the record macros to record the item fields:
	`uvm_record_field("action",      action)     
	`uvm_record_field("data",        data)       
	`uvm_record_field("ecc ",        ecc)       
	`uvm_record_field("full",        full)       
	`uvm_record_field("nearly_full", nearly_full)
endfunction : do_record


function void do_pack(uvm_packer packer);
	super.do_pack(packer);
	`uvm_pack_enum(action)     
	`uvm_pack_int(data)        
	`uvm_pack_int(full)        
	`uvm_pack_int(nearly_full) 
endfunction : do_pack


function void do_unpack(uvm_packer packer);
	super.do_unpack(packer);
	`uvm_unpack_enum(action,     buffer_writer_action_e)
	`uvm_unpack_int(data)                               
	`uvm_unpack_int(full)                               
	`uvm_unpack_int(nearly_full)                        
endfunction : do_unpack


function string convert2string();
	string s;
	$sformat(s, "%s\n", super.convert2string());
	$sformat(s, {"%s\n",
				"action      = %s\n",           
				"data        = 'h%0h  'd%0d\n", 
				"ecc         = 'h%0h  'd%0d\n", 
				"full        = 'h%0h  'd%0d\n", 
				"nearly_full = 'h%0h  'd%0d\n"},
			get_full_name(), action.name, data, data, ecc, ecc, full, full, nearly_full, nearly_full);
	return s;
endfunction : convert2string
