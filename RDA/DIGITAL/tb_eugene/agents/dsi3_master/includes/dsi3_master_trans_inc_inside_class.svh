function void do_copy(uvm_object rhs);
	dsi3_master_tr rhs_;
	if (!$cast(rhs_, rhs))
		`uvm_fatal(get_type_name(), "Cast of rhs object failed")
	super.do_copy(rhs);
	data     = rhs_.data;    
	msg_type = rhs_.msg_type;
	bit_time = rhs_.bit_time;
endfunction : do_copy


function bit do_compare(uvm_object rhs, uvm_comparer comparer);
	bit result;
	dsi3_master_tr rhs_;
	if (!$cast(rhs_, rhs))
		`uvm_fatal(get_type_name(), "Cast of rhs object failed")
	result = super.do_compare(rhs, comparer);
	for (int i = 0; i < data.size; i++)
		result &= comparer.compare_field("data", data[i],    rhs_.data[i],  $bits(data[i]));
	result &= comparer.compare_field("msg_type", msg_type, rhs_.msg_type, $bits(msg_type));
	result &= comparer.compare_field("bit_time", bit_time, rhs_.bit_time, $bits(bit_time));
	return result;
endfunction : do_compare


function void do_print(uvm_printer printer);
	if (printer.knobs.sprint == 0)
		`uvm_info(get_type_name(), convert2string(), UVM_MEDIUM)
	else
		printer.m_string = convert2string();
endfunction : do_print


function void do_record(uvm_recorder recorder);
	string data_string = "";
	super.do_record(recorder);
	
	if(data.size() > 1) begin
		logic[15:0] words[$];
		convert_queue#(1, 16)::convert(data, words, 1);
		foreach(words[i]) begin
			data_string = {data_string, $sformatf("%h", words[i])};
			if(i < words.size() - 1) data_string = {data_string, " "};
		end
	end else begin
		data_string = $sformatf("%b", data[0]);
	end

	`uvm_record_field("data ", data_string)
	`uvm_record_field("msg_type",                     msg_type)
	`uvm_record_field("bit_time", bit_time)
endfunction : do_record


function void do_pack(uvm_packer packer);
	super.do_pack(packer);
	`uvm_pack_sarray(data)   
	`uvm_pack_enum(msg_type)
	`uvm_pack_enum(bit_time)
endfunction : do_pack


function void do_unpack(uvm_packer packer);
	super.do_unpack(packer);
	`uvm_unpack_sarray(data)                            
	`uvm_unpack_enum(msg_type,  dsi3_pkg::dsi3_msg_type)
	`uvm_unpack_enum(bit_time,  dsi3_pkg::dsi3_bit_time_e)
endfunction : do_unpack


function string convert2string();
	string s;
	$sformat(s, "%s\n", super.convert2string());
	$sformat(s, {"%s\n",
				"data     = %p\n", 
				"msg_type = %s\n",
				"bit_time = %s\n"				},
			get_full_name(), data, msg_type.name, bit_time.name);
	return s;
endfunction : convert2string
