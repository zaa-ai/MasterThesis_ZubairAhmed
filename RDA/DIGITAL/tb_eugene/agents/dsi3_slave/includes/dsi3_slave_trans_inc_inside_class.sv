function void post_randomize(); 
	tolerance = (real'(tolerance_int)/1000.0);	// set real tolerance
endfunction  // End of inlined include file	

function void do_copy(uvm_object rhs);
	dsi3_slave_tr rhs_;
	if (!$cast(rhs_, rhs))
		`uvm_fatal(get_type_name(), "Cast of rhs object failed")
	super.do_copy(rhs);
	data                          = rhs_.data;                         
	tolerance_int                 = rhs_.tolerance_int;                
	chiptime                      = rhs_.chiptime;
	chips_per_symbol              = rhs_.chips_per_symbol;
	msg_type                      = rhs_.msg_type;                     
	symbol_coding_error_injection = rhs_.symbol_coding_error_injection;
	chip_length_error_injection = rhs_.chip_length_error_injection;
	symbol_coding_error           = rhs_.symbol_coding_error;          
	tolerance                     = rhs_.tolerance; 	
endfunction : do_copy


function bit do_compare(uvm_object rhs, uvm_comparer comparer);
	bit result;
	dsi3_slave_tr rhs_;
	if (!$cast(rhs_, rhs))
		`uvm_fatal(get_type_name(), "Cast of rhs object failed")
	result = super.do_compare(rhs, comparer);
	for (int i = 0; i < data.size; i++)
		result &= comparer.compare_field("data", data[i],              rhs_.data[i],       $bits(data[i]));
	result &= comparer.compare_field("tolerance_int", tolerance_int, rhs_.tolerance_int, $bits(tolerance_int));
	result &= comparer.compare_field("chiptime", chiptime,           rhs_.chiptime,      $bits(chiptime));
	result &= comparer.compare_field("chips_per_symbol", chips_per_symbol, rhs_.chips_per_symbol, $bits(chips_per_symbol));
	result &= comparer.compare_field("msg_type", msg_type,           rhs_.msg_type,      $bits(msg_type));
	result &= comparer.compare_field("symbol_coding_error_injection", symbol_coding_error_injection, rhs_.symbol_coding_error_injection, $bits(symbol_coding_error_injection));
	result &= comparer.compare_field("chip_length_error_injection",   chip_length_error_injection,   rhs_.chip_length_error_injection,   $bits(chip_length_error_injection));
	result &= comparer.compare_field("symbol_coding_error", symbol_coding_error, rhs_.symbol_coding_error,      $bits(symbol_coding_error));
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
	// Use the record macros to record the item fields:
	for (int i = 0; i < data.size(); i++) begin
		if ((i[1:0]==0) && (i>0))
			data_string = {data_string, " "};
		data_string = {data_string, $sformatf("%h", data[i])};
	end
	`uvm_record_field("data ", data_string)
	`uvm_record_field("symbol_count ", data.size())
	`uvm_record_field("tolerance_int",                tolerance_int)
	`uvm_record_field("chiptime",                     chiptime) 
	`uvm_record_field("chips_per_symbol",             chips_per_symbol) 
	`uvm_record_field("msg_type",                     msg_type)     
	`uvm_record_field("tolerance",                    tolerance)
	`uvm_record_field("symbol_coding_error_injection", symbol_coding_error_injection)
	`uvm_record_field("chip_length_error_injection", chip_length_error_injection)
	`uvm_record_field("symbol_coding_error",          symbol_coding_error)
	begin
		dsi3_chip_distribution distribution = new(data);
		`uvm_record_string("symbol distribution",          distribution.get_string())
	end
endfunction : do_record


function void do_pack(uvm_packer packer);
	super.do_pack(packer);
	`uvm_pack_queue(data)       
	`uvm_pack_int(tolerance_int) 
	`uvm_pack_int(chiptime)  
	`uvm_pack_int(chips_per_symbol)  
	`uvm_pack_enum(msg_type)
	`uvm_pack_enum(symbol_coding_error_injection)
	`uvm_pack_enum(chip_length_error_injection)
	`uvm_pack_int(symbol_coding_error)
endfunction : do_pack


function void do_unpack(uvm_packer packer);
	super.do_unpack(packer);
	`uvm_unpack_queue(data)                               
	`uvm_unpack_int(tolerance_int)                         
	`uvm_unpack_int(chiptime)   
	`uvm_unpack_int(chips_per_symbol)   
	`uvm_unpack_enum(msg_type,     dsi3_pkg::dsi3_msg_type)
	`uvm_unpack_enum(symbol_coding_error_injection,  error_injection_e)
	`uvm_unpack_enum(chip_length_error_injection,  error_injection_e)
	`uvm_unpack_int(symbol_coding_error)
endfunction : do_unpack


function string convert2string();
	string s;
	$sformat(s, "%s\n", super.convert2string());
	$sformat(s, {"%s\n",
				"data          = %p\n",           
				"tolerance_int = 'h%0h  'd%0d\n", 
				"chiptime      = 'h%0h  'd%0d\n",
				"msg_type      = %s\n",           
				"tolerance     = 'h%0h  'd%0d\n",           
				"chips per symbol = 'd%0d\n",
				"symbol_coding_error_injection = %s\n",
				"chip_length_error_injection = %s\n",
				"symbol_coding_error = %1b"
				},
			get_full_name(), data, tolerance_int, tolerance_int, chiptime, chiptime, msg_type.name, tolerance, tolerance, chips_per_symbol, symbol_coding_error_injection, chip_length_error_injection, symbol_coding_error);
	return s;
endfunction : convert2string
