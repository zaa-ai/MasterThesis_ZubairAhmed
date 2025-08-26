/**
 * JTAG seqence for ELIP read access. 
 */
class jtag_read_elip_seq extends jtag_master_default_seq;
	
	rand int unsigned address;
	rand bit	init;
	longint unsigned read_value;
	
	// static event and read values to be checked from within the module scope
	static event check_read;
  
	static longint check_read_value = 0;
	static longint check_expected_value = 0;
  
	static event check_read_byte;
  
	static byte check_read_value_byte = 0;
	static byte check_expected_value_byte = 0;
    
	`uvm_object_utils(jtag_read_elip_seq)
	`uvm_declare_p_sequencer(jtag_master_sequencer)

	constraint address_co		{ address inside{['h00:(2**(p_sequencer.m_config.dr_length_elip_addr)-1)]};}
  
	/************************ Methods declarations ************************/
	function new(string name = "");
		super.new("jtag_read_elip_seq");
	endfunction
  
	/************************ User defined methods declarations ************************/
	virtual task body();
		int unsigned value	=  (address << p_sequencer.m_config.dr_length_elip_data);
		jtag_tr transaction;
		int unsigned dr_length;
		
		if (p_sequencer.m_config.dr_length > (p_sequencer.m_config.dr_length_elip_addr + p_sequencer.m_config.dr_length_elip_data))
			dr_length = p_sequencer.m_config.dr_length;
		else
			dr_length = (p_sequencer.m_config.dr_length_elip_addr + p_sequencer.m_config.dr_length_elip_data);
		
		`uvm_do_with(transaction, {
				ir_length == p_sequencer.m_config.ir_length;
				ir_value == ELIP_RDF;
				dr_value == 266'(value);
				dr_length == local::dr_length;
				init_jtag == init;});
		`uvm_do_with(transaction, {
				ir_length == p_sequencer.m_config.ir_length;
				ir_value == ELIP_RD;
				dr_value == 266'(0);
				dr_length == p_sequencer.m_config.dr_length_elip_data;
				init_jtag == 1'b0;});
		read_value = transaction.read_dr;
    
		`uvm_info(get_type_name(), $sformatf("reading ELIP (%2h) at address %0d (%0h): read %0d (%h0)", transaction.ir_value, address, value, read_value, read_value), UVM_DEBUG)
	endtask : body
	
	function void do_record(uvm_recorder recorder);
		`uvm_record_field("init", init)
		if (addresses_pkg::addresses.exists(address))
			`uvm_record_field("address", addresses_pkg::addresses[address])
		else
			`uvm_record_field("address", address)
		`uvm_record_field("read_value", $sformatf("%16h(%20d)", read_value, read_value))
	endfunction : do_record		

	virtual function void check_value(int expected_value);
		check_read_value = longint'(read_value);
		check_expected_value = longint'(expected_value);
		-> check_read;
		if (int'(read_value) != expected_value) begin
			`uvm_error(get_type_name(), $sformatf("wrong ELIP read at address %5d (%3h): read %4d (%4h), expected %4d (%4h)", address, address, read_value, read_value, expected_value, expected_value));
		end
	endfunction : check_value;
 	
		virtual function void check_value_byte(byte expected_value);
	check_read_value_byte = read_value;
	check_expected_value_byte = expected_value;
	-> check_read_byte;
	if (check_read_value_byte != check_expected_value_byte) begin
		`uvm_error(get_type_name(), $sformatf("wrong ELIP read at address (%3h): read (%4h), expected (%4h)", address, check_read_value_byte, check_expected_value_byte));
	end
	endfunction : check_value_byte; 	
 	  
	virtual function longint get_read_value();
		return read_value;
	endfunction : get_read_value

	virtual function void check_value_masked(int expected_value, int mask);
		check_read_value = read_value & mask;
		check_expected_value = expected_value & mask;
		-> check_read;
		if ((int'(read_value) & mask) != (expected_value & mask)) begin 
			`uvm_error(get_type_name(),	$sformatf("wrong ELIP read at address %5d (%3h): read %4d (%3h), expected %4d (%3h), mask %3d (%3h)", 
					address, address, read_value & mask, read_value & mask, expected_value & mask, expected_value & mask, mask, mask));
		end
	endfunction : check_value_masked;

		virtual function void check_value_range(int expected_min_value, expected_max_value);
	if ((int'(read_value) < expected_min_value) || (int'(read_value) > expected_max_value)) begin 
		`uvm_error(get_type_name(), 
			$sformatf("wrong ELIP read at address %5d (%3h): read %4d (%4h), expected %4d (%4h) ... %4d (%4h)", 
				address, address, read_value, read_value, expected_min_value, expected_min_value, expected_max_value, expected_max_value));
	end
	endfunction : check_value_range;
	
endclass : jtag_read_elip_seq

/**
 * JTAG seqence for ELIP address incremental read access. 
 */
class jtag_read_incr_elip_seq extends jtag_read_elip_seq;
	
	`uvm_object_utils(jtag_read_incr_elip_seq)
	`uvm_declare_p_sequencer(jtag_master_sequencer)

  
	/************************ Methods declarations ************************/
	function new(string name = "");
		super.new("jtag_read_incr_elip_seq");
	endfunction : new
  
	/************************ User defined methods declarations ************************/
	virtual task body();
		jtag_tr transaction;
		
		`uvm_do_with(transaction, {ir_length == p_sequencer.m_config.ir_length; ir_value == ELIP_RDI; dr_value == 266'(0);	dr_length == p_sequencer.m_config.dr_length_elip_data; init_jtag == init;});
		read_value = transaction.read_dr;
    
		`uvm_info(get_type_name(), $sformatf("reading incremental ELIP (%2h): read %0d (%h0)", transaction.ir_value, read_value, read_value), UVM_DEBUG)
	endtask : body
	
endclass : jtag_read_incr_elip_seq

/**
 * JTAG sequence for ELIP write access.
 */
class jtag_write_elip_seq extends jtag_master_default_seq;
	rand int	address;
	rand int	data;
	rand bit	init;
    
	int			read_ir;
	longint		read_data;

	`uvm_object_utils_begin(jtag_write_elip_seq)
	`uvm_field_int(init, UVM_DEFAULT | UVM_NORECORD)
	`uvm_field_int(address, UVM_DEFAULT | UVM_NORECORD | UVM_HEX)
	`uvm_field_int(data, UVM_DEFAULT | UVM_NORECORD | UVM_HEX)
	`uvm_field_int(read_ir, UVM_DEFAULT | UVM_NORECORD | UVM_HEX)
	`uvm_field_int(read_data, UVM_DEFAULT | UVM_NORECORD | UVM_HEX)
	`uvm_object_utils_end
	`uvm_declare_p_sequencer(jtag_master_sequencer)
	
	
	constraint address_co { address inside{[0:(2**(p_sequencer.m_config.dr_length_elip_addr)-1)]};}
	constraint data_co { data inside{['0:(2**(p_sequencer.m_config.dr_length_elip_data)-1)]};}
  
	/************************ Methods declarations ************************/
	function new(string name = "");
		super.new("jtag_write_elip_seq");
	endfunction : new
  
	/************************ User defined methods declarations ************************/
	virtual task body();
		jtag_tr transaction; 
		int dr_length;
		
		if (p_sequencer.m_config.dr_length > (p_sequencer.m_config.dr_length_elip_addr + p_sequencer.m_config.dr_length_elip_data))
			dr_length = p_sequencer.m_config.dr_length;
		else
			dr_length = (p_sequencer.m_config.dr_length_elip_addr + p_sequencer.m_config.dr_length_elip_data);
        
		`uvm_do_with(transaction, {
				ir_value == ELIP_WRF;
				ir_length == p_sequencer.m_config.ir_length;
				dr_length == local::dr_length;
				dr_value == 266'((address << p_sequencer.m_config.dr_length_elip_data) + data);
				init_jtag == init;
			});
        
		read_ir	  = transaction.read_ir;
		read_data = transaction.read_dr;
        
		uvm_report_info(get_type_name(), 
				$sformatf("\nTime: %d us: writing ELIP (%2h) at address %d (%h): write %d (%h)",
					$time()/1us, transaction.ir_value, address, transaction.dr_value, data, data), UVM_DEBUG);
    
	endtask : body
	
	function void do_record(uvm_recorder recorder);
		`uvm_record_field("init", init)
		if (addresses_pkg::addresses.exists(address))
			`uvm_record_field("address", addresses_pkg::addresses[address])
		else
			`uvm_record_field("address", address)
		`uvm_record_field("data", $sformatf("%8h(%10d)", data, data))
		`uvm_record_field("read_ir", $sformatf("%2h", read_ir))
		`uvm_record_field("read_data", $sformatf("%16h(%20d)", read_data, read_data))
	endfunction : do_record	

endclass : jtag_write_elip_seq

/**
 * JTAG seqence for testregister read access. 
 */
class jtag_write_testregister_seq extends jtag_master_default_seq;
	
	`uvm_object_utils(jtag_write_testregister_seq)
	`uvm_declare_p_sequencer(jtag_master_sequencer)
	
	rand longint	data;
	rand bit	init;
    
	int			read_ir;
	longint		read_data;
	
	function new(string name = "");
		super.new("jtag_write_testregister_seq");
	endfunction : new
  
	/************************ User defined methods declarations ************************/
	virtual task body();
		jtag_tr transaction; 
        
		`uvm_do_with(transaction, {
				ir_value == 'hC6;
				ir_length == p_sequencer.m_config.ir_length;
				dr_length == p_sequencer.m_config.dr_length;
				dr_value ==  266'(data);
				init_jtag == init;
			});
        
		read_ir	  = transaction.read_ir;
		read_data = transaction.read_dr;
        
		uvm_report_info(get_type_name(), 
				$sformatf("\nTime: %d us: writing JTAG testregister with IR (%2h): write %d (%h)",
					$time()/1us, transaction.ir_value,  data, data), UVM_DEBUG);
    
	endtask : body
	
	function void do_record(uvm_recorder recorder);
		`uvm_record_field("init", init)
		`uvm_record_field("data", $sformatf("%8h(%10d)", data, data))
		`uvm_record_field("read_ir", $sformatf("%2h", read_ir))
		`uvm_record_field("read_data", $sformatf("%16h(%20d)", read_data, read_data))
	endfunction : do_record		
	
endclass : jtag_write_testregister_seq