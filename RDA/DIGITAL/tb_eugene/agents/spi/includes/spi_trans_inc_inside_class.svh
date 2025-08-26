function void do_copy(uvm_object rhs);
	spi_tr rhs_;
	if (!$cast(rhs_, rhs)) `uvm_fatal(get_type_name(), "Cast of rhs object failed")
	super.do_copy(rhs);
	tr_type  = rhs_.tr_type;
	data_in  = rhs_.data_in;               
	data_out = rhs_.data_out;
	word_index = rhs_.word_index;
	bit_count = rhs_.bit_count;
endfunction : do_copy


function bit do_compare(uvm_object rhs, uvm_comparer comparer);
	bit result;
	spi_tr rhs_;
	if (!$cast(rhs_, rhs)) `uvm_fatal(get_type_name(), "Cast of rhs object failed")
	result = super.do_compare(rhs, comparer);
	result &= comparer.compare_field("tr_type",  tr_type,  rhs_.tr_type,  $bits(tr_type));
	result &= comparer.compare_field("data_in",  data_in,  rhs_.data_in,  $bits(data_in));
	result &= comparer.compare_field("data_out", data_out, rhs_.data_out, $bits(data_out));
	result &= comparer.compare_field("word_index", word_index, rhs_.word_index, $bits(word_index));
	result &= comparer.compare_field("bit_count", bit_count, rhs_.bit_count, $bits(bit_count));
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
	`uvm_record_field("tr_type", tr_type)       
	`uvm_record_int("data_in", data_in, 16, UVM_HEX)
	`uvm_record_int("data_out", data_out, 16, UVM_HEX)
	`uvm_record_int("word_index", word_index, 16, UVM_DEC)
	`uvm_record_int("bit_count", bit_count, 16, UVM_DEC)
endfunction : do_record

function string convert2string();
	string s;
	$sformat(s, "%s\n", super.convert2string());
	$sformat(s, {"%s\n",
				"type       = %p\n", 
				"data_in    = 0x%0h\n",           
				"data_out   = 0x%0h\n",
				"word_index = %0d\n",
				"bit_count = %0d\n"}, get_full_name(), tr_type, data_in, data_out, word_index, bit_count);
	return s;
endfunction : convert2string

function void do_pack(uvm_packer packer);
	super.do_pack(packer);
endfunction

function void do_unpack(uvm_packer packer);
	super.do_unpack(packer);
endfunction
